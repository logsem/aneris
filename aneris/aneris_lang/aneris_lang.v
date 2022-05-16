From aneris.aneris_lang Require Export lang.

Canonical Structure aneris_ectxi_lang := EctxiLanguage head_step config_step locale_of aneris_lang_mixin.
Canonical Structure aneris_ectx_lang := EctxLanguageOfEctxi aneris_ectxi_lang.
Canonical Structure aneris_lang := LanguageOfEctx aneris_ectx_lang.
