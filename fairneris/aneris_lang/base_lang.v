From fairneris.aneris_lang Require Export lang.

Canonical Structure base_ectxi_lang := EctxiLanguage base_lang.head_step base_config_step base_lang.locale_of base_lang.base_config_enabled base_mixin.
Canonical Structure base_ectx_lang := EctxLanguageOfEctxi base_ectxi_lang.
Canonical Structure base_lang := LanguageOfEctx base_ectx_lang.
