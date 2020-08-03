From aneris.aneris_lang Require Export lang.

Canonical Structure ground_ectxi_lang := EctxiLanguage base_mixin.
Canonical Structure ground_ectx_lang := EctxLanguageOfEctxi ground_ectxi_lang.
Canonical Structure ground_lang := LanguageOfEctx ground_ectx_lang.
