import WPFiniteLaurentDifferential

open scoped LaurentPolynomial
open LaurentPolynomial WPFiniteLaurentDifferential

namespace WPFieldAssembly.SourceClosureBalancedNativeAlgebra

set_option maxHeartbeats 1600000

/-- Six times f times the native particular, before any division by the actual f. -/
noncomputable def clearedParticular {R : Type*} [CommRing R]
    (f G P delta T0 Tproper : R) : R :=
  6*f^2*T0-3*f^2*P^2-3*G^2-6*f*G*P+6*G*delta+2*f*Tproper

/-- The complete differentiated numerator; its two factors of f remain explicit. -/
noncomputable def clearedParticularDerivative {R : Type*} [CommRing R]
    (f G P delta T0 Tproper df dG dP ddelta dT0 dTproper : R) : R :=
  12*f*df*T0+6*f^2*dT0-6*f*df*P^2-6*f^2*P*dP-6*G*dG-
    6*(df*G*P+f*dG*P+f*G*dP)+6*(dG*delta+G*ddelta)+
      2*(df*Tproper+f*dTproper)

theorem clearedParticular_derivative {K : Type*} [Field K]
    (f G P delta T0 Tproper : K[T;T⁻¹]) :
    D (clearedParticular f G P delta T0 Tproper)=
      clearedParticularDerivative f G P delta T0 Tproper
        (D f) (D G) (D P) (D delta) (D T0) (D Tproper) := by
  have h2 : D (2 : K[T;T⁻¹])=0 := by simpa only [map_ofNat] using D_C (2 : K)
  have h3 : D (3 : K[T;T⁻¹])=0 := by simpa only [map_ofNat] using D_C (3 : K)
  have h6 : D (6 : K[T;T⁻¹])=0 := by simpa only [map_ofNat] using D_C (6 : K)
  simp only [clearedParticular,clearedParticularDerivative,pow_two,map_add,map_sub,D_mul,
    h2,h3,h6,zero_mul,zero_add]
  ring

/-- The native proper primitive and the original UV source give exactly SB99's forcing.
All equations are multiplied out, so no root or CM inverse is used. -/
theorem cleared_particular_source {R : Type*} [CommRing R]
    (f G H U L Gamma delta S P T0 Tproper sigma TB TBv phase h xinv
      df dG dP ddelta dT0 dTproper : R)
    (hmetric : L*(f*dG-G*df)=U*f*(1-f))
    (hproper : L*(f*dTproper-Tproper*df)=
      U*(3*(f*P+G-delta)+h*f^2*(1-phase)+f*(TB-TBv)))
    (hP : 2*L*dP=2*U-L*xinv)
    (hUV : 2*L*dT0=2*L*sigma-2*Gamma*S+L*xinv*(S-P))
    (hseed : G+H+f*S=0) :
    L*(f*clearedParticularDerivative f G P delta T0 Tproper
        df dG dP ddelta dT0 dTproper-
      2*clearedParticular f G P delta T0 Tproper*df)=
        6*f^3*L*sigma-6*Gamma*f^3*S-3*L*f^2*H*xinv+
          6*f*L*G*ddelta-6*L*G*delta*df-6*f^2*U*delta+
          2*h*f^3*U*(1-phase)+2*f^2*U*(TB-TBv) := by
  dsimp only [clearedParticular,clearedParticularDerivative]
  linear_combination
    3*f^3*hUV-3*(f^3*P+f^2*G)*hP+
      6*(delta-G-f*P)*hmetric+2*f*hproper+3*L*f^2*xinv*hseed

/-- The full proper expansion factors the cleared numerator by f, retaining both high phases. -/
theorem native_particular_factorization {R : Type*} [CommRing R]
    (f G H K Kv A B n2 nv2 Tp Tpv JL JLv S P delta T0 Tlocal Tref shift : R)
    (hSquare : G^2=f*K^2*n2)
    (hLocal : 2*f*Tlocal=2*G*A+f*K*Tp*n2+2*f^2*K*JL)
    (hRef : 2*f*Tref=2*H*B+f*shift*Kv*Tpv*nv2+2*f^2*Kv*JLv)
    (hDelta : 3*delta=3*f*P+3*G-A+B)
    (hSeed : G+H+f*S=0) :
    clearedParticular f G P delta T0 (Tlocal+Tref)=
      f*(6*f*T0-3*f*P^2-2*S*B+K*(3*K+Tp)*n2+
        shift*Kv*Tpv*nv2+2*f*(K*JL+Kv*JLv)) := by
  dsimp only [clearedParticular]
  linear_combination 2*G*hDelta+hLocal+hRef+3*hSquare+2*B*hSeed

/-- Equal actual forcing gives the homogeneous ratio equation before dividing by f. -/
theorem same_forcing_cleared_ratio {K : Type*} [Field K]
    (f L E Q forcing : K[T;T⁻¹]) (hL : L≠0)
    (hE : 6*f*L*(f*D E-E*D f)=forcing)
    (hQ : L*(f*D Q-2*Q*D f)=forcing) :
    f*D (Q-6*f*E)-2*(Q-6*f*E)*D f=0 := by
  apply mul_left_cancel₀ hL
  simp only [mul_zero]
  have h6 : D (6 : K[T;T⁻¹])=0 := by simpa only [map_ofNat] using D_C (6 : K)
  simp only [map_sub,D_mul,h6,zero_mul,zero_add]
  linear_combination hQ-hE

/-- The full reflected numerator retains precisely the proper seed defect. -/
theorem native_cleared_reflected_identity {R : Type*} [CommRing R]
    (f G P S delta T0 Tproper : R) :
    clearedParticular f (-f*S-G) (S-P) (-delta) T0 Tproper=
      clearedParticular f G P delta T0 Tproper+6*f*S*delta := by
  unfold clearedParticular
  ring

end WPFieldAssembly.SourceClosureBalancedNativeAlgebra
