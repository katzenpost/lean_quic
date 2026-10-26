/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import LeanTLS.Alert

namespace LeanQUIC

/-! # Transport errors (RFC 9000 §20.1) -/

inductive TransportError where
  | noError
  | internalError
  | connectionRefused
  | flowControl
  | streamLimit
  | streamState
  | finalSize
  | frameEncoding
  | transportParameter
  | connectionIdLimit
  | protocolViolation
  | invalidToken
  | cryptoBufferExceeded
  | keyUpdate
  | aeadLimitReached
  /-- A TLS alert, sent as `0x0100 + alert` (RFC 9001 §4.8). -/
  | crypto (alert : LeanTLS.Alert)
deriving DecidableEq, Repr, Inhabited

namespace TransportError

def code : TransportError → Nat
  | noError => 0x0
  | internalError => 0x1
  | connectionRefused => 0x2
  | flowControl => 0x3
  | streamLimit => 0x4
  | streamState => 0x5
  | finalSize => 0x6
  | frameEncoding => 0x7
  | transportParameter => 0x8
  | connectionIdLimit => 0x9
  | protocolViolation => 0xa
  | invalidToken => 0xb
  | cryptoBufferExceeded => 0xd
  | keyUpdate => 0xe
  | aeadLimitReached => 0xf
  | crypto a => 0x100 + a.code.toNat

end TransportError

end LeanQUIC
