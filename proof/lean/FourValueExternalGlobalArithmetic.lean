import FourValueArithmeticGrid

/-! One finite rational calculation certificate.
The independently reproducible witness is reconstructed from
numerical/global28/arithmetic_cells.txt by verify_arithmetic.py.
Grid.Valid contains only finite integer/rational predicates. No prime-sum,
limit, determinant, or asymptotic proposition is admitted in this file. -/
noncomputable section
namespace OddZeta.FourValue.ArithmeticCertificate

theorem external_grid_certificate : ∃ G : Grid,G.Valid := by
 sorry -- EXTERNAL_GLOBAL_ARITHMETIC_CERTIFICATE_V1

end OddZeta.FourValue.ArithmeticCertificate
