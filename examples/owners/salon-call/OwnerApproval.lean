import SpecTools.OwnerApproval

namespace SalonOwner
open Lean Elab Command
open SpecTools.OwnerApproval SpecTools.Audit

def Reviewed.cutoff : Nat := 2
def Reviewed.onlineBooking (noShows : Nat) : Prop := noShows < Reviewed.cutoff
def Current.onlineBooking (noShows : Nat) : Prop := noShows < 2

def files : Files :=
  { subject := "salon online booking", revision := "2",
    prose := "examples/owners/salon-call/owner-requirements.md",
    coverage := "examples/owners/salon-call/owner-coverage.json" }

def bindings : List ApprovedContract := [⟨`SalonOwner.Current.onlineBooking, `SalonOwner.Reviewed.onlineBooking⟩]

#eval show CommandElabM Unit from do
  match ← IO.getEnv "ELENXIS_OWNER_APPROVAL_DIR" with
  | none => IO.println (toJson (← capture files bindings)).compress
  | some raw =>
    let dir := System.FilePath.mk raw
    check files bindings ⟨"synthetic-owner", dir / "receipt.json", dir / "receipt.json.sig",
      dir / "allowed_signers"⟩

end SalonOwner
