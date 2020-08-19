From aneris.aneris_lang Require Export lang.

Canonical Structure base_ectxi_lang := EctxiLanguage base_mixin.
Canonical Structure base_ectx_lang := EctxLanguageOfEctxi base_ectxi_lang.
Canonical Structure base_lang := LanguageOfEctx base_ectx_lang.
