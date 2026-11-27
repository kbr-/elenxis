-- SPDX-License-Identifier: Apache-2.0
import ProofInventory

axiom unsupportedInventoryEvidence : False

theorem mustBeRejected : False := unsupportedInventoryEvidence

#eval SpecTools.ProofInventory.check [``mustBeRejected]
