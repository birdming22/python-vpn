import argparse, asyncio, io, os, enum, struct, collections, hashlib, ipaddress, socket, random, base64, itertools, hmac
import pproxy
from . import enums, message, crypto, ip
from .__doc__ import *

class State(enum.Enum):
    INITIAL = 0
    SA_SENT = 1
    ESTABLISHED = 2
    DELETED = 3
    KE_SENT = 4
    HASH_SENT = 5
    AUTH_SET = 6
    CONF_SENT = 7
    CHILD_SA_SENT = 8

class ChildSa:
    def __init__(self, spi_in, spi_out, crypto_in, crypto_out):
        self.spi_in = spi_in
        self.spi_out = spi_out
        self.crypto_in = crypto_in
        self.crypto_out = crypto_out
        self.msgid_in = 1
        self.msgid_out = 1
        self.msgwin_in = set()
        self.child = None
    def incr_msgid_in(self):
        self.msgid_in += 1
        while self.msgid_in in self.msgwin_in:
            self.msgwin_in.discard(self.msgid_in)
            self.msgid_in += 1

class IKEv1Session:
    all_child_sa = {}
    def __init__(self, args, sessions, peer_spi):
        self.args = args
        self.sessions = sessions
        self.my_spi = os.urandom(8)
        self.peer_spi = peer_spi
        self.crypto = None
        self.my_nonce = os.urandom(32)
        self.peer_nonce = None
        self.child_sa = []
        self.state = State.INITIAL
        self.sessions[self.my_spi] = self
    def response(self, exchange, payloads, message_id=0, *, crypto=None, hashmsg=None):
        if hashmsg:
            message_id = message_id or random.randrange(1<<32)
            buf = (b'' if hashmsg is True else hashmsg) + message.Message.encode_payloads(payloads)
            hash_r = self.crypto.prf.prf(self.skeyid_a, message_id.to_bytes(4, 'big') + buf)
            payloads.insert(0, message.PayloadHASH_1(hash_r))
        response = message.Message(self.peer_spi, self.my_spi, 0x10, exchange,
                                   enums.MsgFlag.NONE, message_id, payloads)
        #print(repr(response))
        return response.to_bytes(crypto=crypto)
    def verify_hash(self, request):
        payload_hash = request.payloads.pop(0)
        assert payload_hash.type == enums.Payload.HASH_1
        hash_i = self.crypto.prf.prf(self.skeyid_a, request.message_id.to_bytes(4, 'big') + message.Message.encode_payloads(request.payloads))
        assert hash_i == payload_hash.data
    def xauth_init(self):
        attrs = { enums.CPAttrType.XAUTH_TYPE: 0,
                  enums.CPAttrType.XAUTH_USER_NAME: b'',
                  enums.CPAttrType.XAUTH_USER_PASSWORD: b'',
                }
        response_payloads = [message.PayloadCP_1(enums.CFGType.CFG_REQUEST, attrs)]
        return self.response(enums.Exchange.TRANSACTION_1, response_payloads, crypto=self.crypto, hashmsg=True)
    def process(self, request, stream, remote_id, reply):
        request.parse_payloads(stream, crypto=self.crypto)
        print(repr(request))
        if remote_id not in self.all_child_sa:
            self.all_child_sa[remote_id] = self.child_sa
        elif self.all_child_sa[remote_id] != self.child_sa:
            self.child_sa = self.all_child_sa[remote_id]
        if request.exchange == enums.Exchange.IDENTITY_1 and request.get_payload(enums.Payload.SA_1):
            assert self.state == State.INITIAL
            request_payload_sa = request.get_payload(enums.Payload.SA_1)
            self.sa_bytes = request_payload_sa.to_bytes()
            self.transform = request_payload_sa.proposals[0].transforms[0].values
            self.auth_mode = self.transform[enums.TransformAttr.AUTH]
            del request_payload_sa.proposals[0].transforms[1:]
            response_payloads = request.payloads
            reply(self.response(enums.Exchange.IDENTITY_1, response_payloads))
            self.state = State.SA_SENT
        elif request.exchange == enums.Exchange.IDENTITY_1 and request.get_payload(enums.Payload.KE_1):
            assert self.state == State.SA_SENT
            self.peer_public_key = request.get_payload(enums.Payload.KE_1).ke_data
            self.my_public_key, self.shared_secret = crypto.DiffieHellman(self.transform[enums.TransformAttr.DH], self.peer_public_key)
            self.peer_nonce = request.get_payload(enums.Payload.NONCE_1).nonce
            response_payloads = [ message.PayloadKE_1(self.my_public_key), message.PayloadNONCE_1(self.my_nonce),
                                  message.PayloadNATD_1(os.urandom(32)), message.PayloadNATD_1(os.urandom(32)) ]
            cipher = crypto.Cipher(self.transform[enums.TransformAttr.ENCR], self.transform[enums.TransformAttr.KEY_LENGTH])
            prf = crypto.Prf(self.transform[enums.TransformAttr.HASH])
            self.skeyid = prf.prf(self.args.passwd.encode(), self.peer_nonce+self.my_nonce)
            self.skeyid_d = prf.prf(self.skeyid, self.shared_secret+self.peer_spi+self.my_spi+bytes([0]))
            self.skeyid_a = prf.prf(self.skeyid, self.skeyid_d+self.shared_secret+self.peer_spi+self.my_spi+bytes([1]))
            self.skeyid_e = prf.prf(self.skeyid, self.skeyid_a+self.shared_secret+self.peer_spi+self.my_spi+bytes([2]))
            iv = prf.hasher(self.peer_public_key+self.my_public_key).digest()[:cipher.block_size]
            self.crypto = crypto.Crypto(cipher, self.skeyid_e[:cipher.key_size], prf=prf, iv=iv)
            reply(self.response(enums.Exchange.IDENTITY_1, response_payloads))
            self.state = State.KE_SENT
        elif request.exchange == enums.Exchange.IDENTITY_1 and request.get_payload(enums.Payload.ID_1):
            assert self.state == State.KE_SENT
            payload_id = request.get_payload(enums.Payload.ID_1)
            prf = self.crypto.prf
            hash_i = prf.prf(self.skeyid, self.peer_public_key+self.my_public_key+self.peer_spi+self.my_spi+self.sa_bytes+payload_id.to_bytes())
            assert hash_i == request.get_payload(enums.Payload.HASH_1).data, 'Authentication Failed'
            response_payload_id = message.PayloadID_1(enums.IDType.ID_FQDN, f'{__title__}-{__version__}'.encode())
            hash_r = prf.prf(self.skeyid, self.my_public_key+self.peer_public_key+self.my_spi+self.peer_spi+self.sa_bytes+response_payload_id.to_bytes())
            response_payloads = [response_payload_id, message.PayloadHASH_1(hash_r)]
            reply(self.response(enums.Exchange.IDENTITY_1, response_payloads, crypto=self.crypto))
            self.state = State.HASH_SENT
            if self.auth_mode == enums.AuthId_1.XAUTHInitPreShared:
                reply(self.xauth_init())
        elif request.exchange == enums.Exchange.TRANSACTION_1:
            self.verify_hash(request)
            payload_cp = request.get_payload(enums.Payload.CP_1)
            if enums.CPAttrType.XAUTH_USER_NAME in payload_cp.attrs:
                assert self.state == State.HASH_SENT
                response_payloads = [ message.PayloadCP_1(enums.CFGType.CFG_SET, {enums.CPAttrType.XAUTH_STATUS: 1}) ]
                self.state = State.AUTH_SET
            elif enums.CPAttrType.INTERNAL_IP4_ADDRESS in payload_cp.attrs:
                assert self.state == State.AUTH_SET
                attrs = { enums.CPAttrType.INTERNAL_IP4_ADDRESS: ipaddress.ip_address('10.0.0.1').packed,
                          enums.CPAttrType.INTERNAL_IP4_DNS: ipaddress.ip_address(self.args.dns).packed,
                        }
                response_payloads = [ message.PayloadCP_1(enums.CFGType.CFG_REPLY, attrs, identifier=payload_cp.identifier) ]
                self.state = State.CONF_SENT
            elif payload_cp.cftype == enums.CFGType.CFG_ACK:
                return
            else:
                raise Exception('Unknown CP Exchange')
            reply(self.response(enums.Exchange.TRANSACTION_1, response_payloads, request.message_id, crypto=self.crypto, hashmsg=True))
        elif request.exchange == enums.Exchange.QUICK_1 and len(request.payloads) == 1:
            assert request.payloads[0].type == enums.Payload.HASH_1
            assert self.state == State.CHILD_SA_SENT
            self.state = State.ESTABLISHED
        elif request.exchange == enums.Exchange.QUICK_1:
            assert self.state == State.CONF_SENT and self.auth_mode == enums.AuthId_1.XAUTHInitPreShared or \
                   self.state == State.HASH_SENT and self.auth_mode == enums.AuthId_1.PSK or \
                   self.child_sa
            self.verify_hash(request)
            payload_nonce = request.get_payload(enums.Payload.NONCE_1)
            peer_nonce = payload_nonce.nonce
            payload_nonce.nonce = my_nonce = os.urandom(len(peer_nonce))
            chosen_proposal = request.get_payload(enums.Payload.SA_1).proposals[0]
            del chosen_proposal.transforms[1:]
            peer_spi = chosen_proposal.spi
            chosen_proposal.spi = my_spi = os.urandom(4)
            reply(self.response(enums.Exchange.QUICK_1, request.payloads, request.message_id, crypto=self.crypto, hashmsg=peer_nonce))

            transform = chosen_proposal.transforms[0].values
            cipher = crypto.Cipher(chosen_proposal.transforms[0].id, transform[enums.ESPAttr.KEY_LENGTH])
            integ = crypto.Integrity(transform[enums.ESPAttr.AUTH])
            keymat_fmt = struct.Struct('>{0}s{1}s'.format(cipher.key_size, integ.key_size))
            keymat = self.crypto.prf.prfplus(self.skeyid_d, bytes([chosen_proposal.protocol])+my_spi+peer_nonce+my_nonce, False)
            sk_ei, sk_ai = keymat_fmt.unpack(bytes(next(keymat) for _ in range(keymat_fmt.size)))
            keymat = self.crypto.prf.prfplus(self.skeyid_d, bytes([chosen_proposal.protocol])+peer_spi+peer_nonce+my_nonce, False)
            sk_er, sk_ar = keymat_fmt.unpack(bytes(next(keymat) for _ in range(keymat_fmt.size)))
            crypto_in = crypto.Crypto(cipher, sk_ei, integ, sk_ai)
            crypto_out = crypto.Crypto(cipher, sk_er, integ, sk_ar)
            child_sa = ChildSa(my_spi, peer_spi, crypto_in, crypto_out)
            self.sessions[my_spi] = child_sa
            for old_child_sa in self.child_sa:
                old_child_sa.child = child_sa
            self.child_sa.append(child_sa)
            self.state = State.CHILD_SA_SENT
        elif request.exchange == enums.Exchange.INFORMATIONAL_1:
            self.verify_hash(request)
            response_payloads = []
            delete_payload = request.get_payload(enums.Payload.DELETE_1)
            notify_payload = request.get_payload(enums.Payload.NOTIFY_1)
            if not request.payloads:
                pass
            elif delete_payload and delete_payload.protocol == enums.Protocol.IKE:
                self.state = State.DELETED
                self.sessions.pop(self.my_spi)
                response_payloads.append(delete_payload)
                message_id = request.message_id
            elif delete_payload:
                spis = []
                for spi in delete_payload.spis:
                    child_sa = next((x for x in self.child_sa if x.spi_out == spi), None)
                    if child_sa:
                        self.child_sa.remove(child_sa)
                        self.sessions.pop(child_sa.spi_in)
                        spis.append(child_sa.spi_in)
                response_payloads.append(message.PayloadDELETE_1(delete_payload.doi, delete_payload.protocol, spis))
                message_id = request.message_id
            elif notify_payload and notify_payload.notify == enums.Notify.ISAKMP_NTYPE_R_U_THERE:
                notify_payload.notify = enums.Notify.ISAKMP_NTYPE_R_U_THERE_ACK
                response_payloads.append(notify_payload)
                message_id = request.message_id
                message_id = None
            elif notify_payload and notify_payload.notify == enums.Notify.INITIAL_CONTACT_1:
                notify_payload.notify = enums.Notify.INITIAL_CONTACT_1
                response_payloads.append(notify_payload)
                message_id = request.message_id
            else:
                raise Exception(f'unhandled informational {request!r}')
            reply(self.response(enums.Exchange.INFORMATIONAL_1, response_payloads, message_id, crypto=self.crypto, hashmsg=True))
            #if notify_payload and notify_payload.notify == enums.Notify.INITIAL_CONTACT_1:
            #    reply(self.xauth_init())
        else:
            raise Exception(f'unhandled request {request!r}')

class IKEv2Session:
    def __init__(self, args, sessions, peer_spi):
        self.args = args
        self.sessions = sessions
        #self.my_spi = os.urandom(8)
        self.my_spi = bytes.fromhex('1b93e12ae42672b8')
        self.peer_spi = peer_spi
        self.peer_msgid = 0
        self.my_crypto = None
        self.peer_crypto = None
        #self.my_nonce = os.urandom(32)
        self.my_nonce = bytes.fromhex('0da0543dddedd8cb8f078a562d5bd4ae0f71ca90122a6a1bf0eef82d05afb9fc')
        self.peer_nonce = None
        self.state = State.INITIAL
        self.request_data = None
        self.response_data = None
        self.child_sa = []
        print(self.my_spi.hex())
        self.sessions[self.my_spi] = self
    def create_key(self, ike_proposal, shared_secret, old_sk_d=None):
        prf = crypto.Prf(ike_proposal.get_transform(enums.Transform.PRF).id)
        integ = crypto.Integrity(ike_proposal.get_transform(enums.Transform.INTEG).id)
        cipher = crypto.Cipher(ike_proposal.get_transform(enums.Transform.ENCR).id,
                               ike_proposal.get_transform(enums.Transform.ENCR).keylen)
        if not old_sk_d:
            skeyseed = prf.prf(self.peer_nonce+self.my_nonce, shared_secret)
        else:
            skeyseed = prf.prf(old_sk_d, shared_secret+self.peer_nonce+self.my_nonce)
        keymat_fmt = struct.Struct('>{0}s{1}s{1}s{2}s{2}s{0}s{0}s'.format(prf.key_size, integ.key_size, cipher.key_size))
        keymat = prf.prfplus(skeyseed, self.peer_nonce+self.my_nonce+self.peer_spi+self.my_spi)
        self.sk_d, sk_ai, sk_ar, sk_ei, sk_er, sk_pi, sk_pr = keymat_fmt.unpack(bytes(next(keymat) for _ in range(keymat_fmt.size)))
        print(f'skeyseed={skeyseed.hex()}')
        print(f'sk_ei={sk_ei.hex()}')
        print(f'sk_er={sk_er.hex()}')
        print(f'sk_ai={sk_ai.hex()}')
        print(f'sk_ar={sk_ar.hex()}')
        self.my_crypto = crypto.Crypto(cipher, sk_er, integ, sk_ar, prf, sk_pr)
        self.peer_crypto = crypto.Crypto(cipher, sk_ei, integ, sk_ai, prf, sk_pi)
    def create_child_key(self, child_proposal, nonce_i, nonce_r):
        integ = crypto.Integrity(child_proposal.get_transform(enums.Transform.INTEG).id)
        cipher = crypto.Cipher(child_proposal.get_transform(enums.Transform.ENCR).id,
                               child_proposal.get_transform(enums.Transform.ENCR).keylen)
        keymat_fmt = struct.Struct('>{0}s{1}s{0}s{1}s'.format(cipher.key_size, integ.key_size))
        keymat = self.my_crypto.prf.prfplus(self.sk_d, nonce_i+nonce_r)
        sk_ei, sk_ai, sk_er, sk_ar = keymat_fmt.unpack(bytes(next(keymat) for _ in range(keymat_fmt.size)))
        crypto_in = crypto.Crypto(cipher, sk_ei, integ, sk_ai)
        crypto_out = crypto.Crypto(cipher, sk_er, integ, sk_ar)
        child_sa = ChildSa(os.urandom(4), child_proposal.spi, crypto_in, crypto_out)
        self.child_sa.append(child_sa)
        self.sessions[child_sa.spi_in] = child_sa
        return child_sa
    def auth_data(self, message_data, nonce, payload, sk_p):
        prf = self.peer_crypto.prf.prf
        return prf(prf(self.args.passwd.encode(), b'Key Pad for IKEv2'), message_data+nonce+prf(sk_p, payload.to_bytes()))
    def response(self, exchange, payloads, *, crypto=None):
        response = message.Message(self.peer_spi, self.my_spi, 0x20, exchange,
                                   enums.MsgFlag.Response, self.peer_msgid, payloads)
        #print(repr(response))
        self.peer_msgid += 1
        self.response_data = response.to_bytes(crypto=crypto)
        return self.response_data
    def process(self, request, stream, remote_id, reply):
        if request.message_id == self.peer_msgid - 1:
            reply(self.response_data)
            return
        elif request.message_id != self.peer_msgid:
            return
        request.parse_payloads(stream, crypto=self.peer_crypto)
        print(repr(request))
        if request.exchange == enums.Exchange.IKE_SA_INIT:
            assert self.state == State.INITIAL
            self.peer_nonce = request.get_payload(enums.Payload.NONCE).nonce
            chosen_proposal = request.get_payload(enums.Payload.SA).get_proposal(enums.EncrId.ENCR_AES_CBC)
            print('======================================')
            print('proposal: ', chosen_proposal.to_repr())
            print('======================================')
            payload_ke = request.get_payload(enums.Payload.KE)
            prefered_dh = chosen_proposal.get_transform(enums.Transform.DH).id
            if payload_ke.dh_group != prefered_dh or payload_ke.ke_data[0] == 0:
                reply(self.response(enums.Exchange.IKE_SA_INIT, [ message.PayloadNOTIFY(0, enums.Notify.INVALID_KE_PAYLOAD, b'', prefered_dh.to_bytes(2, 'big'))]))
                return
            public_key, shared_secret = crypto.DiffieHellman(payload_ke.dh_group, payload_ke.ke_data)
            self.create_key(chosen_proposal, shared_secret)
            response_payloads = [ message.PayloadSA([chosen_proposal]),
                                  message.PayloadNONCE(self.my_nonce),
                                  message.PayloadKE(payload_ke.dh_group, public_key),
                                  message.PayloadNOTIFY(0, enums.Notify.NAT_DETECTION_DESTINATION_IP, b'', os.urandom(20)),
                                  message.PayloadNOTIFY(0, enums.Notify.NAT_DETECTION_SOURCE_IP, b'', os.urandom(20)) ]
            #reply(self.response(enums.Exchange.IKE_SA_INIT, response_payloads))
            self.response(enums.Exchange.IKE_SA_INIT, response_payloads)
            self.state = State.SA_SENT
            self.request_data = stream.getvalue()
        elif request.exchange == enums.Exchange.IKE_AUTH:
            assert self.state == State.SA_SENT
            request_payload_idi = request.get_payload(enums.Payload.IDi)
            request_payload_auth = request.get_payload(enums.Payload.AUTH)
            if request_payload_auth is None:
                EAP = True
                raise Exception('EAP not supported')
            else:
                EAP = False
                auth_data = self.auth_data(self.request_data, self.my_nonce, request_payload_idi, self.peer_crypto.sk_p)
                assert auth_data == request_payload_auth.auth_data, 'Authentication Failed'
            chosen_child_proposal = request.get_payload(enums.Payload.SA).get_proposal(enums.EncrId.ENCR_AES_CBC)
            child_sa = self.create_child_key(chosen_child_proposal, self.peer_nonce, self.my_nonce)
            chosen_child_proposal.spi = child_sa.spi_in
            response_payload_idr = message.PayloadIDr(enums.IDType.ID_FQDN, f'{__title__}-{__version__}'.encode())
            auth_data = self.auth_data(self.response_data, self.peer_nonce, response_payload_idr, self.my_crypto.sk_p)

            response_payloads = [ message.PayloadSA([chosen_child_proposal]),
                                  request.get_payload(enums.Payload.TSi),
                                  request.get_payload(enums.Payload.TSr),
                                  response_payload_idr,
                                  message.PayloadAUTH(enums.AuthMethod.PSK, auth_data) ]
            if request.get_payload(enums.Payload.CP):
                attrs = { enums.CPAttrType.INTERNAL_IP4_ADDRESS: ipaddress.ip_address('1.0.0.1').packed,
                          enums.CPAttrType.INTERNAL_IP4_DNS: ipaddress.ip_address(self.args.dns).packed, }
                response_payloads.append(message.PayloadCP(enums.CFGType.CFG_REPLY, attrs))
            reply(self.response(enums.Exchange.IKE_AUTH, response_payloads, crypto=self.my_crypto))
            self.state = State.ESTABLISHED
        elif request.exchange == enums.Exchange.INFORMATIONAL:
            assert self.state == State.ESTABLISHED
            response_payloads = []
            delete_payload = request.get_payload(enums.Payload.DELETE)
            if not request.payloads:
                pass
            elif delete_payload and delete_payload.protocol == enums.Protocol.IKE:
                self.state = State.DELETED
                self.sessions.pop(self.my_spi)
                for child_sa in self.child_sa:
                    self.sessions.pop(child_sa.spi_in)
                self.child_sa = []
                response_payloads.append(delete_payload)
            elif delete_payload:
                spis = []
                for spi in delete_payload.spis:
                    child_sa = next((x for x in self.child_sa if x.spi_out == spi), None)
                    if child_sa:
                        self.child_sa.remove(child_sa)
                        self.sessions.pop(child_sa.spi_in)
                        spis.append(child_sa.spi_in)
                response_payloads.append(message.PayloadDELETE(delete_payload.protocol, spis))
            else:
                raise Exception(f'unhandled informational {request!r}')
            reply(self.response(enums.Exchange.INFORMATIONAL, response_payloads, crypto=self.my_crypto))
        elif request.exchange == enums.Exchange.CREATE_CHILD_SA:
            assert self.state == State.ESTABLISHED
            chosen_proposal = request.get_payload(enums.Payload.SA).get_proposal(enums.EncrId.ENCR_AES_CBC)
            if chosen_proposal.protocol != enums.Protocol.IKE:
                payload_notify = request.get_payload_notify(enums.Notify.REKEY_SA)
                if not payload_notify:
                    raise Exception(f'unhandled protocol {chosen_proposal.protocol} {request!r}')
                old_child_sa = next(i for i in self.child_sa if i.spi_out == payload_notify.spi)
                peer_nonce = request.get_payload(enums.Payload.NONCE).nonce
                my_nonce = os.urandom(random.randrange(16, 256))
                child_sa = self.create_child_key(chosen_proposal, peer_nonce, my_nonce)
                chosen_proposal.spi = child_sa.spi_in
                old_child_sa.child = child_sa
                response_payloads = [ message.PayloadNOTIFY(chosen_proposal.protocol, enums.Notify.REKEY_SA, old_child_sa.spi_in, b''),
                                      message.PayloadNONCE(my_nonce),
                                      message.PayloadSA([chosen_proposal]),
                                      request.get_payload(enums.Payload.TSi),
                                      request.get_payload(enums.Payload.TSr) ]
            else:
                child = IKEv2Session(self.args, self.sessions, chosen_proposal.spi)
                child.state = State.ESTABLISHED
                child.peer_nonce = request.get_payload(enums.Payload.NONCE).nonce
                child.child_sa = self.child_sa
                self.child_sa = []
                payload_ke = request.get_payload(enums.Payload.KE)
                public_key, shared_secret = crypto.DiffieHellman(payload_ke.dh_group, payload_ke.ke_data)
                chosen_proposal.spi = child.my_spi
                child.create_key(chosen_proposal, shared_secret, self.sk_d)
                response_payloads = [ message.PayloadSA([chosen_proposal]),
                                      message.PayloadNONCE(child.my_nonce),
                                      message.PayloadKE(payload_ke.dh_group, public_key) ]
            reply(self.response(enums.Exchange.CREATE_CHILD_SA, response_payloads, crypto=self.my_crypto))
        else:
            raise Exception(f'unhandled request {request!r}')

IKE_HEADER = b'\x00\x00\x00\x00'

class IKE_500(asyncio.DatagramProtocol):
    def __init__(self, args, sessions):
        self.args = args
        self.sessions = sessions
    def connection_made(self, transport):
        self.transport = transport
    def datagram_received(self, data, addr, *, response_header=b''):
        stream = io.BytesIO(data)
        request = message.Message.parse(stream)
        print(f"spi_i={request.spi_i.hex()}")
        print(f"spi_r={request.spi_r.hex()}")
        if request.exchange == enums.Exchange.IKE_SA_INIT:
            session = IKEv2Session(self.args, self.sessions, request.spi_i)
        elif request.exchange == enums.Exchange.IDENTITY_1 and request.spi_r == bytes(8):
            session = IKEv1Session(self.args, self.sessions, request.spi_i)
        elif request.spi_r in self.sessions:
            session = self.sessions[request.spi_r]
        else:
            return
        #session.process(request, stream, addr[:2], lambda response: self.transport.sendto(response_header+response, addr))
        session.process(request, stream, addr[:2], None)


class SPE_4500(IKE_500):
    def __init__(self, args, sessions):
        IKE_500.__init__(self, args, sessions)
        self.ippacket = ip.IPPacket(args)
    def datagram_received(self, data, addr):
        spi = data[:4]
        if spi == b'\xff':
            self.transport.sendto(b'\xff', addr)
        elif spi == IKE_HEADER:
            IKE_500.datagram_received(self, data[4:], addr, response_header=IKE_HEADER)
        elif spi in self.sessions:
            sa = self.sessions[spi]
            seqnum = int.from_bytes(data[4:8], 'big')
            if seqnum < sa.msgid_in or seqnum in sa.msgwin_in:
                return
            if sa.msgid_in == 1 and sa.crypto_in.integrity.hasher is hashlib.sha256 and (len(data)-8)%16 == 12:
                # HMAC-SHA2-256-96 fix
                sa.crypto_in.integrity.hash_size = 12
                sa.crypto_out.integrity.hash_size = 12
            sa.crypto_in.verify_checksum(data)
            if seqnum > sa.msgid_in + 65536:
                sa.incr_msgid_in()
            if seqnum == sa.msgid_in:
                sa.incr_msgid_in()
            else:
                sa.msgwin_in.add(seqnum)
            header, data = sa.crypto_in.decrypt_esp(data[8:])
            def reply(data):
                nonlocal sa
                while sa and sa.spi_in not in self.sessions:
                    sa = sa.child
                if not sa:
                    return False
                encrypted = bytearray(sa.crypto_out.encrypt_esp(header, data))
                encrypted[0:0] = sa.spi_out + sa.msgid_out.to_bytes(4, 'big')
                sa.crypto_out.add_checksum(encrypted)
                sa.msgid_out += 1
                self.transport.sendto(encrypted, addr)
                return True
            self.ippacket.handle(addr[:2], header, data, reply)
        else:
            print('unknown packet', data, addr)

class WIREGUARD(asyncio.DatagramProtocol):
    def __init__(self, args):
        self.args = args
        self.preshared_key = b'\x00'*32
        self.ippacket = ip.IPPacket(args)
        self.private_key = hashlib.blake2s(args.passwd.encode()).digest()
        self.public_key = crypto.X25519(self.private_key, 9)
        self.keys = {}
        self.index_generators = {}
        self.sender_index_generator = itertools.count()
        print('======== WIREGUARD SETTING ========')
        print('PublicKey:', base64.b64encode(self.public_key).decode())
        print('===================================')
    def connection_made(self, transport):
        self.transport = transport
    def datagram_received(self, data, addr):
        cmd = int.from_bytes(data[0:4], 'little')
        if cmd == 1 and len(data) == 148:
            HASH = lambda x: hashlib.blake2s(x).digest()
            MAC  = lambda key, x: hashlib.blake2s(x, key=key, digest_size=16).digest()
            HMAC = lambda key, x: hmac.digest(key, x, hashlib.blake2s)
            p, mac1, mac2 = struct.unpack('<116s16s16s', data)
            assert mac1 == MAC(HASH(b"mac1----" + self.public_key), p)
            assert mac2 == b'\x00'*16
            index = next(self.sender_index_generator)
            sender_index, unencrypted_ephemeral, encrypted_static, encrypted_timestamp = struct.unpack('<4xI32s48s28s', data[:-32])

            chaining_key = HASH(b"Noise_IKpsk2_25519_ChaChaPoly_BLAKE2s")
            hash0 = HASH(HASH(HASH(chaining_key + b"WireGuard v1 zx2c4 Jason@zx2c4.com") + self.public_key) + unencrypted_ephemeral)
            chaining_key = HMAC(HMAC(chaining_key, unencrypted_ephemeral), b"\x01")
            temp = HMAC(chaining_key, crypto.X25519(self.private_key, unencrypted_ephemeral))
            chaining_key = HMAC(temp, b"\x01")
            static_public = crypto.aead_chacha20poly1305_decrypt(HMAC(temp, chaining_key + b"\x02"), 0, encrypted_static, hash0)
            hash0 = HASH(hash0 + encrypted_static)
            temp = HMAC(chaining_key, crypto.X25519(self.private_key, static_public))
            chaining_key = HMAC(temp, b"\x01")
            timestamp = crypto.aead_chacha20poly1305_decrypt(HMAC(temp, chaining_key + b"\x02"), 0, encrypted_timestamp, hash0)
            hash0 = HASH(hash0 + encrypted_timestamp)

            ephemeral_private = os.urandom(32)
            ephemeral_public = crypto.X25519(ephemeral_private, 9)
            hash0 = HASH(hash0 + ephemeral_public)
            chaining_key = HMAC(HMAC(HMAC(HMAC(HMAC(HMAC(chaining_key, ephemeral_public), b"\x01"), crypto.X25519(ephemeral_private, unencrypted_ephemeral)), b"\x01"), crypto.X25519(ephemeral_private, static_public)), b"\x01")
            temp = HMAC(chaining_key, self.preshared_key)
            chaining_key = HMAC(temp, b"\x01")
            temp2 = HMAC(temp, chaining_key + b"\x02")
            key = HMAC(temp, temp2 + b"\x03")
            hash0 = HASH(hash0 + temp2)
            encrypted_nothing = crypto.aead_chacha20poly1305_encrypt(key, 0, b"", hash0)
            #hash0 = HASH(hash0 + encrypted_nothing)
            msg = struct.pack('<III32s16s', 2, index, sender_index, ephemeral_public, encrypted_nothing)
            msg = msg + MAC(HASH(b"mac1----" + static_public), msg) + b'\x00'*16
            self.transport.sendto(msg, addr)
            print('login', addr, sender_index)

            temp = HMAC(chaining_key, b"")
            receiving_key = HMAC(temp, b"\x01")
            sending_key = HMAC(temp, receiving_key + b"\x02")
            self.keys[index] = (sender_index, receiving_key, sending_key)
            self.index_generators[index] = itertools.count()
        elif cmd == 4 and len(data) >= 32:
            _, index, counter = struct.unpack('<IIQ', data[:16])
            sender_index, receiving_key, sending_key = self.keys[index]
            packet = crypto.aead_chacha20poly1305_decrypt(receiving_key, counter, data[16:], b'')
            def reply(data):
                counter = next(self.index_generators[index])
                data = data + b'\x00'*((-len(data))%16)
                msg = crypto.aead_chacha20poly1305_encrypt(sending_key, counter, data, b'')
                msg = struct.pack('<IIQ', 4, sender_index, counter) + msg
                self.transport.sendto(msg, addr)
                return True
            if packet:
                self.ippacket.handle_ipv4(addr[:2], packet, reply)
            else:
                reply(b'')


def main():
    parser = argparse.ArgumentParser(description=__description__, epilog=f'Online help: <{__url__}>')
    parser.add_argument('-wg', dest='wireguard', default=None, type=int, help='start a wireguard vpn with port number (default: off)')
    parser.add_argument('-r', dest='rserver', default=[], action='append', type=pproxy.Connection, help='tcp remote server uri (default: direct)')
    parser.add_argument('-ur', dest='urserver', default=[], action='append', type=pproxy.Connection, help='udp remote server uri (default: direct)')
    parser.add_argument('-s', dest='salgorithm', default='fa', choices=('fa', 'rr', 'rc', 'lc'), help='scheduling algorithm (default: first_available)')
    parser.add_argument('-p', dest='passwd', default='vpn-password', help='password (default: vpn-password)')
    parser.add_argument('-dns', dest='dns', default='1.1.1.1', help='dns server (default: 1.1.1.1)')
    parser.add_argument('-nc', dest='nocache', default=None, action='store_true', help='do not cache dns (default: off)')
    parser.add_argument('-v', dest='v', action='count', help='print verbose output')
    parser.add_argument('--version', action='version', version=f'{__title__} {__version__}')
    args = parser.parse_args()
    args.DIRECT = pproxy.DIRECT
    loop = asyncio.get_event_loop()
    sessions = {}
    transport1, _ = loop.run_until_complete(loop.create_datagram_endpoint(lambda: IKE_500(args, sessions), ('0.0.0.0', 500)))
    transport2, _ = loop.run_until_complete(loop.create_datagram_endpoint(lambda: SPE_4500(args, sessions), ('0.0.0.0', 4500)))
    print('Serving on UDP :500 :4500...')
    if args.wireguard:
        transport3, _ = loop.run_until_complete(loop.create_datagram_endpoint(lambda: WIREGUARD(args), ('0.0.0.0', args.wireguard)))
        print(f'Serving on UDP :{args.wireguard} (WIREGUARD)...')
    else:
        transport3 = None
    try:
        loop.run_forever()
    except KeyboardInterrupt:
        print('exit')
    for task in asyncio.all_tasks(loop) if hasattr(asyncio, 'all_tasks') else asyncio.Task.all_tasks():
        task.cancel()
    transport1.close()
    transport2.close()
    if transport3:
        transport3.close()
    loop.run_until_complete(loop.shutdown_asyncgens())
    loop.close()

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__description__, epilog=f'Online help: <{__url__}>')
    parser.add_argument('-wg', dest='wireguard', default=None, type=int, help='start a wireguard vpn with port number (default: off)')
    parser.add_argument('-r', dest='rserver', default=[], action='append', type=pproxy.Connection, help='tcp remote server uri (default: direct)')
    parser.add_argument('-ur', dest='urserver', default=[], action='append', type=pproxy.Connection, help='udp remote server uri (default: direct)')
    parser.add_argument('-s', dest='salgorithm', default='fa', choices=('fa', 'rr', 'rc', 'lc'), help='scheduling algorithm (default: first_available)')
    parser.add_argument('-p', dest='passwd', default='test', help='password (default: test)')
    parser.add_argument('-dns', dest='dns', default='1.1.1.1', help='dns server (default: 1.1.1.1)')
    parser.add_argument('-nc', dest='nocache', default=None, action='store_true', help='do not cache dns (default: off)')
    parser.add_argument('-v', dest='v', action='count', help='print verbose output')
    parser.add_argument('--version', action='version', version=f'{__title__} {__version__}')
    args = parser.parse_args()
    args.DIRECT = pproxy.DIRECT
    sessions = {}
    sa_init = bytes.fromhex('ffdd80a0846265dc00000000000000002120220800000000000003402200026002000120010100200300000c0100000c800e00800300000c0100000c800e00c00300000c0100000c800e01000300000c01000017800e00800300000c01000017800e00c00300000c01000017800e01000300000801000003030000080300000c030000080300000d030000080300000e030000080300000203000008030000050300000803000008030000080200000503000008020000060300000802000007030000080200000403000008020000080300000802000002030000080400001303000008040000140300000804000015030000080400001c030000080400001d030000080400001e030000080400001f0300000804000020030000080400000f030000080400001003000008040000110300000804000012000000080400000e020001140201001d0300000c01000014800e00800300000c01000014800e00c00300000c01000014800e0100030000080100001c0300000c01000013800e00800300000c01000013800e00c00300000c01000013800e01000300000c01000012800e00800300000c01000012800e00c00300000c01000012800e0100030000080200000503000008020000060300000802000007030000080200000403000008020000080300000802000002030000080400001303000008040000140300000804000015030000080400001c030000080400001d030000080400001e030000080400001f0300000804000020030000080400000f030000080400001003000008040000110300000804000012000000080400000e0000002803010004030000080100000303000008030000010300000802000001000000080400000228000048001300000f0a9a047a37811d3a2ba3add7ee5144d56e62ebcf164fdc3ea216a501cebd5580ea120d5fc712f04daa7ca9227ce723d6203a091edc2e7cdce3cb39c25cddf6290000249e11e1adf161760cf0b5934f9a45accb258b1bcba1bf1f1fe27be2c88d9c6b6a2900001c00004004875a2ed7da60f77ec1f33d4dbabf2bc9b494cc582900001c000040050a8133237dcdb02e1aae8249a661f3bdb4e8eb8b290000080000402e290000100000402f00020003000400050000000800004016')
    #sa_init = bytes.fromhex('b565ff59207697620d0f8994d11ceafa212022200000000000000110220000300000002c010100040300000c0100000c800e0080030000080300000c030000080200000400000008040000132800004800130000410b72b8247181375736f988c6edaba2e8bbe9d56bbbcd4724fd99ccbe744d1e607d0bbd321f09f863863334b974ff9ad1a8e3f22d6771767f8ae1f38e8c52ee290000247c2527f142220b24ab69698fe81f33cef153ec4e857c408c49e1d1d0433f81522900001c00004004a867b4d4f75549bd2a2fa3218dcda1e7d314a2d82900001c00004005ab2b416edb84d4d79052d15e27533272c228a313290000080000402e290000100000402f00020003000400050000000800004014')
    ike500 = IKE_500(args, sessions)
    ike500.datagram_received(sa_init, ('127.0.0.1', 500))
    spi = bytes.fromhex('617a54106527ea14')
    for k, v in sessions.items():
        sessions[spi] = v
        break
    ike_auth = bytes.fromhex('00000000ffdd80a0846265dc1b93e12ae42672b82e20230800000001000001a02300018448b71c250943027bfbe1d794885c5672b1dee2489b9e6a93e3d42c3ea65449d73d93a7ca5100b3075de32e91fc3aaf7616b128d59b5b6adfd3bda2700dc6cf6d15cc84e4cc93478737cdd27f03057f0b66c28c54eb03702b7afe97753b54ac2fd4a57e4e8f184880856de9b4d19f09159442b81f5a22a92eecb66a20786c6e9b679f2a1e2391b3b09dd7cc8c1d6094746e6de20fa84434eb6ac7a704ee658a35cabcbe4faf1ae8206c6432a3521b56eb179b941e97eda6818de1b4cd2bf6707a5278c659e22774e16dfd5fea14a996fbe5f599c4cb64b679874ed0ccf7232ee1278cd105811816c94b42845e9df846137855ef2c6141b9e794737eec9bf5f3ee75ec131eb32716b8b26334effb5d417be80d8195c9fc9734f8e94aec7d38087225d4a59186029851caeebb1111ec614b6b7054bebce3537b8a96e761fffaa2e90ca32a4339f918f9e80ed788ae3b0c35d5e2f63faa9962f33fdc0f4589082f81ee751e543abd697cff16af7c21f2e23ab23711a61aecd411cbf57fceb41cd435')
    #ike_auth = bytes.fromhex('00000000b565ff59207697620d0f8994d11ceafa3520232000000001000004d4240004b800010002fd22a8581d97a1ec5da538119fae39e65914372269998feeff0c25022139b2fba37f44301699ccc746729d1f0bf52f96b791bbdc44e78964fd44d25644deb40f83d6ae76457eb6bd6c64b60e84c34a71af58170706e6c48916a5e2c7f27a8a48e997aa3a5610dde6f59279a5602520e3b6f4458b4bb2f1e4fddaa9dfc00447bff6fb1cf45ae6add25a5730afb295f88a917627d3e23a89bf4a88cc3fcb576db80a9238ab94c8e54926f48ab1c16169261be431258074225d32726c266815de69c855a56d25a4f4f6526241334dd621095dd8b5c140facf991f8144b0c6c6a5a5682114f909c719c7a7ca2962e3e3fe0131556e49ff8a4dab201547309f043bbcdc754847e436ae17d33fe1537bd8239257fd004ec14978043904c37dcb3e2eedcf17ab166e4e8d86f28c2c6dae55de4ed6f54d76b8290e3b70c7e8d9dad1c46e072046ce4ab4c294e9713cbf337b8fb120570377ed15ac30956584562a8ba689d0e8d02ac16f288b7131c84db15dc0a4b17f7b32a6f0ac275c59d91a2b3da801f38f1a58c4d32e5b9ecdd4b6c0aa4f135f048583a7b763df0ede00a195349347838e92d62520a48ec73858423ccd629270f21e54d82a5e41999d44dc2bc68aaa07564cc39ae30ce71c4cf3b30c3a1db6fb69b5410b7069aa746e70806a5ce16f856959cf296daa9814a0fae9ad1e50432f507fdf122fee9b9482b36386481bfcfd41392dad3570f0ba35a7fa77f4993a1bf5782bf5874d87281a54000dfc644f24842f937f06624767fda3b87f9b54a8c745f224686d5c679acb9500560abca3028f75787700cf6836f5420e0c3f137371a5c2aa0a80975b4d635cd8ae9aceb986bf3b1c9175c05ebe37c8ae2a6b8a50c173379eabd9a594fa30cab1a9ea9e048a48ac556b4a800662dd8e75cf681b3b107c75e6bed03ed2a3299e6806e75752b49a8dd7a75393cfad8adfdffa126f64a72d3953a4ae7b8e6e0c2a54d57e4ab297955a74b91f0217687cb8c3c81c51d2db248f3579a7bd2435b2dec253166f417fb7c46f4c6d6bcda7d798ebfd6c8c14220cdbbde2cd52c6f4b71a7d585177f572e84f76259b0a8609c4872bee0961fd5f7e559ee6a0d3fb8a431dfe29cfeb09fc9f5e3eb0c18adaa2e6819e87c1b2d847ff7d4127555bbf36b38a98a87bc03e80cb6a52e7a2b4c96dee0378fa0fe96b8d9b43224ede1bf4897e3861ad6e5153e60547dfefd01cc5b1ce04794afb84a9cc8f77e662a6ac6446b6f2f4af7aafafb12092555d6c0f0e833d1a880e2a5459ca4208cbb965063c376c092558bd47364d13a57681e9e49bf171f33ac7fe2fcbe2660af581894eccc68c89a20db5896928751c5c8f0af069fba2b27a8757345319ddb83493dd8e30ce6a1df9dbe9a2c83f94903e67cb95babbf2951c3278b136997a01519aed4d10f05e94d29fc95a93f0714714531d3b6299d1b54abfe36aaafb4e7442eca7d9d1a7f8963827b23e3c08cae8769b287466b6e0b1cbc4c647937aa0c096c5cee40ddda88f07815ceb43e0151c12fe6b27f544035e1b355cee65966eca5302aee9645d140613d3d431b1f87231eab572233a50f7034266f4f6dc964495020d2721973ee5195f6dc9ac72ac07808f877e57bfeb3ca2941b73431d3004dae0cbdc91a04a485c1d64a3a0594d87293256e9a4405063c3ca52fe4357')
    spe4500 = SPE_4500(args, sessions)
    spe4500.datagram_received(ike_auth, ('127.0.0.1', 4500))
