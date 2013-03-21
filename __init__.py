#!/usr/bin/python
# -*- coding: utf-8 -*-
# Copyright © 2011 Andrew D. Yates
# All Rights Reserved
"""XMLDSig: Sign and Verify XML digital cryptographic signatures.

xmldsig is a minimal implementation of bytestring cryptographic
xml digital signatures which I have written to handle the Google
Application Single Sign On service in Security Assertion Markup
Language. (Google Apps, SSO, SAML respectively).

In this module, all XML must be in Bytestring XML Format:

Bytestring XML Format
=====================
* XML is a utf-8 encoded bytestring.
* XML namespaces must explicitly define all xmlns prefix names
* XML is in minimum whitespace representation.
* <Signature> always signs the entire xml string
* <Signature> is always enveloped as the first child of root
  see: http://www.w3.org/2000/09/xmldsig#enveloped-signature

Note that whitespace, character case, and encoding are significant in
Bytestring XML: e.g. "<b>text</b>" is not the same as "<b> text</b>".

References
==========
* [DI]
  http://www.di-mgt.com.au/xmldsig.html
  Signing an XML document using XMLDSIG
* [RFC 2437]
  http://www.ietf.org/rfc/rfc2437.txt
  PKCS #1: RSA Cryptography Specifications
* [RFC 3275]
  http://www.ietf.org/rfc/rfc3275.txt
  (Extensible Markup Language) XML-Signature Syntax and Processing
* [RSA-SHA1]
  http://www.w3.org/TR/2008/REC-xmldsig-core-20080610/#sec-PKCS1
  XML Signature Syntax and Processing (Second Edition)
  Section: 6.4.2 PKCS1 (RSA-SHA1)
"""

import hashlib
import re
import int_to_bytes as itb
import lxml.etree as ET
import StringIO


RX_ROOT = re.compile('<[^> ]+ ?([^>]*)>')
RX_NS = re.compile('xmlns:[^> ]+')
RX_SIGNATURE = re.compile('<Signature.*?</Signature>')
RX_SIGNED_INFO = re.compile('<SignedInfo.*?</SignedInfo>')
RX_SIG_VALUE = re.compile('<SignatureValue[^>]*>([^>]+)</SignatureValue>')
RX_CAN_VALUE = re.compile('<CanonicalizationMethod Algorithm=([^>]+)[^>]*>')

# SHA1 digest with ASN.1 BER SHA1 algorithm designator prefix [RSA-SHA1]
PREFIX = '\x30\x21\x30\x09\x06\x05\x2B\x0E\x03\x02\x1A\x05\x00\x04\x14'

# Pattern Map:
#   xmlns_attr: xml name space definition attributes including ' ' prefix
#   digest_value: padded hash of message in base64
PTN_SIGNED_INFO_XML = '<SignedInfo xmlns="http://www.w3.org/2000/09/xmldsig#"%(xmlns_attr)s><CanonicalizationMethod Algorithm="%(canonicalization_method)s%(with_comments)s"></CanonicalizationMethod><SignatureMethod Algorithm="http://www.w3.org/2000/09/xmldsig#rsa-sha1"></SignatureMethod><Reference URI=""><Transforms><Transform Algorithm="http://www.w3.org/2000/09/xmldsig#enveloped-signature"></Transform><Transform Algorithm="%(canonicalization_method)s"/></Transforms><DigestMethod Algorithm="http://www.w3.org/2000/09/xmldsig#sha1"></DigestMethod><DigestValue>%(digest_value)s</DigestValue></Reference></SignedInfo>'

# Pattern Map:
#   signed_info_xml: str <SignedInfo> bytestring xml
#   signature_value: str computed signature from <SignedInfo> in base64
#   key_info_xml: str <KeyInfo> bytestring xml of signing key information
#   signature_id: str in form `Id="VALUE" ` (trailing space required) or ""
PTN_SIGNATURE_XML = '<Signature %(signature_id)sxmlns="http://www.w3.org/2000/09/xmldsig#">%(signed_info_xml)s<SignatureValue>%(signature_value)s</SignatureValue>%(key_info_xml)s</Signature>'

# Pattern Map:
#   modulus: str signing RSA key modulus in base64
#   exponent: str signing RSA key exponent in base64
PTN_KEY_INFO_RSA_KEY = '<KeyInfo><KeyValue><RSAKeyValue><Modulus>%(modulus)s</Modulus><Exponent>%(exponent)s</Exponent></RSAKeyValue></KeyValue></KeyInfo>'

# Pattern Map:
#   cert_b64: str of X509 encryption certificate in base64
#   subject_name_xml: str <X509SubjectName> bytstring xml or ""
PTN_KEY_INFO_X509_CERT = '<KeyInfo><X509Data>%(subject_name_xml)s<X509Certificate>%(cert_b64)s</X509Certificate></X509Data></KeyInfo>'

# Pattern Map:
#   cert_b64: str of X509 encryption certificate in base64
#   subject_name_xml: str <X509SubjectName> bytstring xml or ""
#   modulus: str signing RSA key modulus in base64
#   exponent: str signing RSA key exponent in base64
PTN_KEY_INFO = '<KeyInfo><X509Data>%(subject_name_xml)s<X509Certificate>%(cert_b64)s</X509Certificate></X509Data><KeyValue><RSAKeyValue><Modulus>%(modulus)s</Modulus><Exponent>%(exponent)s</Exponent></RSAKeyValue></KeyValue></KeyInfo>'

# Pattern Map:
#   subject_name: str of <SubjectName> value
PTN_X509_SUBJECT_NAME = '<X509SubjectName>%(subject_name)s</X509SubjectName>'

C14N_10 = 'http://www.w3.org/TR/2001/REC-xml-c14n-20010315#'
C14N_11 = 'http://www.w3.org/2006/12/xml-c14n11#'
C14N_10_EXCLUSIVE = 'http://www.w3.org/2001/10/xml-exc-c14n#'


b64d = lambda s: s.decode('base64')

def b64e(s):
  if type(s) in (int, long):
    s = itb.int_to_bytes(s)
  return s.encode('base64').replace('\n', '')

def sign(xml, f_private, key_info_xml, key_size, sig_id_value=None, canonicalization=0, with_comments=True):
  """Return xmldsig XML string from xml_string of XML.

  Args:
    xml: str of bytestring xml to sign
    f_private: func of RSA key private function
    key_size: int of RSA key modulus size in bits (usually 128, 256, 1024, 2048, etc.)
    key_info_xml: str of <KeyInfo> bytestring xml including public key
    sig_id_value: str of signature id value
    canonicalization: the canonicalization to use, 0 => 1.0, 1 => 1.0 exclusive, 2 => 1.1
    with_comments: if comments should be supported in the canonicalization or not
  Returns:
    str: signature bytestring xml
  """
  xml = _convert_xml(xml, canonicalization, with_comments)
  signed_info_xml = _signed_info(xml, canonicalization, with_comments)
  signed = _signed_value(signed_info_xml, key_size)
  signature_value = f_private(signed)

  if sig_id_value is None:
    signature_id = ""
  else:
    signature_id = 'Id="%s" ' % sig_id_value

  signature_xml = PTN_SIGNATURE_XML % {
    'signed_info_xml': signed_info_xml,
    'signature_value': b64e(signature_value),
    'key_info_xml': key_info_xml,
    'signature_id': signature_id,
  }

  return _convert_xml(signature_xml, canonicalization, with_comments)


def verify(xml, f_public, key_size):
  """Return if <Signature> is valid for `xml`

  Args:
    xml: str of XML with xmldsig <Signature> element
    f_public: func from RSA key public function
    key_size: int of RSA key modulus size in bits
  Returns:
    bool: signature for `xml` is valid
  """
  signature_xml = RX_SIGNATURE.search(xml).group(0)
  unsigned_xml = xml.replace(signature_xml, '')

  canonicalization_xml = RX_CAN_VALUE.search(signature_xml).group(1)
  canonicalization = _parse_canonicalization(canonicalization_xml)
  with_comments = _parse_with_comments(canonicalization_xml)

  # compute the given signed value
  signature_value = RX_SIG_VALUE.search(signature_xml).group(1)
  expected = f_public(b64d(signature_value))

  # compute the actual signed value
  signed_info_xml = _signed_info(unsigned_xml, canonicalization, with_comments)
  actual = _signed_value(signed_info_xml, key_size)
  print "E: "  + expected == actual
  return expected == actual

def _parse_canonicalization(canonicalization_xml):
  if canonicalization_xml.find(C14N_11) >= 0:
    return 2
  elif canonicalization_xml.find(C14N_10_EXCLUSIVE) >= 0:
    return 1
  elif canonicalization_xml.find(C14N_10) >= 0:
    return 0
  else:
    throw("Unsupported canonicalization")

def _parse_with_comments(canonicalization_xml):
  return canonicalization_xml.find("WithComments") > 0

def key_info_xml(modulus, exponent, cert_b64, subject_name=None):
  """Return <KeyInfo> xml bytestring using raw public RSA key and RSA X509
  certificate.

  Args:
    modulus: str of bytes
    exponent: str of bytes
    cert_b64: str of certificate contents in base64
    subject_name: str of value of <X509SubjectName> or None
  Returns:
    str of bytestring xml
  """
  if subject_name is None:
    subject_name_xml = ""
  else:
    subject_name_xml = PTN_X509_SUBJECT_NAME % {
      'subject_name': subject_name,
      }

  xml = PTN_KEY_INFO % {
    'modulus': b64e(modulus),
    'exponent': b64e(exponent),
    'cert_b64': cert_b64,
    'subject_name_xml': subject_name_xml,
    }
  return xml

def key_info_xml_rsa(modulus, exponent):
  """Return <KeyInfo> xml bytestring using raw public RSA key.

  Args:
    modulus: str of bytes
    exponent: str of bytes
  Returns:
    str of bytestring xml
  """
  xml = PTN_KEY_INFO_RSA_KEY % {
    'modulus': b64e(modulus),
    'exponent': b64e(exponent),
    }
  return xml


def key_info_xml_cert(cert_b64, subject_name=None):
  """Return <KeyInfo> xml bytestring using RSA X509 certificate.

  Args:
    cert_b64: str of certificate contents in base64
    subject_name: str of value of <X509SubjectName> or None
  """
  if subject_name is None:
    subject_name_xml = ""
  else:
    subject_name_xml = PTN_X509_SUBJECT_NAME % {
      'subject_name': subject_name,
      }
  xml = PTN_KEY_INFO_X509_CERT % {
    'cert_b64': cert_b64,
    'subject_name_xml': subject_name_xml,
    }
  return xml


def _digest(data):
  """SHA1 hash digest of message data.

  Implements RFC2437, 9.2.1 EMSA-PKCS1-v1_5, Step 1. for "Hash = SHA1"

  Args:
    data: str of bytes to digest
  Returns:
    str: of bytes of digest from `data`
  """
  hasher = hashlib.sha1()
  hasher.update(data)
  return hasher.digest()


def _get_xmlns_prefixes(xml):
  """Return string of root namespace prefix attributes in given order.

  Args:
    xml: str of bytestring xml
  Returns:
    str: [xmlns:prefix="uri"] list ordered as in `xml`
  """
  root_attr = RX_ROOT.match(xml).group(1)
  ns_attrs = [a for a in root_attr.split(' ') if RX_NS.match(a)]
  return ' '.join(ns_attrs)


def _signed_info(xml, canonicalization, with_comments):
  """Return <SignedInfo> for bytestring xml.

  Args:
    xml: str of bytestring
    canonicalization: the canonicalization to use, 0 => 1.0, 1 => 1.0 exclusive, 2 => 1.1
    with_comments: if comments should be supported in the canonicalization or not
  Returns:
    str: xml bytestring of <SignedInfo> computed from `xml`
  """
  xmlns_attr = _get_xmlns_prefixes(xml)
  if xmlns_attr:
    xmlns_attr = ' %s' % xmlns_attr

  signed_info_xml = PTN_SIGNED_INFO_XML % {
    'xmlns_attr': xmlns_attr,
    'digest_value': b64e(_digest(xml)),
    'canonicalization_method': _canonicalization_method(canonicalization),
    'with_comments': _with_comments(with_comments),
  }
  return _convert_xml(signed_info_xml, canonicalization, with_comments)


def _canonicalization_method(canonicalization):
  if canonicalization == 0:
    return C14N_10
  elif canonicalization == 1:
    return C14N_10_EXCLUSIVE
  else:
    return C14N_11

def _with_comments(with_comments):
  if with_comments:
    return 'WithComments'
  else:
    return ''

def _signed_value(data, key_size):
  """Return unencrypted rsa-sha1 signature value `padded_digest` from `data`.

  The resulting signed value will be in the form:
  (01 | FF* | 00 | prefix | digest) [RSA-SHA1]
  where "digest" is of the generated c14n xml for <SignedInfo>.

  Args:
    data: str of bytes to sign
    key_size: int of key length in bits; => len(`data`) + 3
  Returns:
    str: rsa-sha1 signature value of `data`
  """
  asn_digest = PREFIX + _digest(data)

  # Pad to "one octet shorter than the RSA modulus" [RSA-SHA1]
  # WARNING: key size is in bits, not bytes!
  padded_size = key_size/8 - 1
  pad_size = padded_size - len(asn_digest) - 2
  pad = '\x01' + '\xFF' * pad_size + '\x00'
  padded_digest = pad + asn_digest

  return padded_digest

def _convert_xml(xml, canonicalization, with_comments):
  et     = ET.fromstring(xml).getroottree()
  output = StringIO.StringIO()
  et.write_c14n(output, exclusive=canonicalization, with_comments=with_comments)
  return output.getvalue()
