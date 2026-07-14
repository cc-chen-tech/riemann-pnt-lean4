import RiemannPNT

namespace PrimeNumberTheorem

example : PNTForm3 :=
  PNTForm3_proved

example : PNTForm2 :=
  PNTForm2_proved

example : PNTForm1 :=
  PNTForm1_proved

example : PNTForm1 ∧ PNTForm2 ∧ PNTForm3 :=
  pnt_forms_proved

example : PNTForm1 ∧ PNTForm2 ∧ PNTForm3 :=
  RiemannPNT.API.pnt_forms_proved

end PrimeNumberTheorem
