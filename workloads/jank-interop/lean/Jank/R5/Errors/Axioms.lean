import Jank.R5.Errors.Theorems

/-! The axioms of round 5's error theorems (`lake env lean Jank/R5/Errors/Axioms.lean`). -/

open Jank.R5.Errors.Theorems

#print axioms object_catch_misses_error_ref
#print axioms object_catch_misses_std
#print axioms default_catch_binds_nil
#print axioms jank_read_string_never_object
#print axioms clj_read_string_throws_iff
#print axioms read_empty_differs
#print axioms load_module_converts
#print axioms jank_failed_require_keeps_ns
#print axioms clj_failed_require_removes_ns
#print axioms jLoadLib_instance
#print axioms jank_delay_native_then_string
#print axioms jank_delay_err_runs
#print axioms clj_delay_once_after
#print axioms clj_delay_once
#print axioms jank_future_terminates
#print axioms jank_future_native_string
#print axioms clj_future_wraps
#print axioms jank_def_meta_always
#print axioms clj_def_meta_none_on_raise
#print axioms ex_info_nil_message
#print axioms ex_data_of_nil_data
#print axioms star_e_of_error_ref
