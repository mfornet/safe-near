import Spec.Authorization

namespace WNear

@[blueprint "thm:balance-authorization"
  (statement := /-- \cref{spec:balance-authorization} holds. -/)]
theorem balance_authorization : BalanceAuthorization := by
  sorry

@[blueprint "thm:registration-authorization"
  (statement := /-- \cref{spec:registration-authorization} holds. -/)]
theorem registration_authorization : RegistrationAuthorization := by
  sorry

end WNear
