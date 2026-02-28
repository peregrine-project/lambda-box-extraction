From Peregrine Require DeserializeCommon.
From Peregrine Require DeserializeEAst.
From Peregrine Require DeserializeExAst.
From Peregrine Require DeserializePAst.
From Peregrine Require DeserializeConfig.
From Peregrine Require CeresExtra.



Definition string_of_error := CeresExtra.string_of_error.

Definition PAst_of_string := DeserializePAst.PAst_of_string.

Definition config_of_string := DeserializeConfig.config'_of_string.

Definition backend_config_of_string := DeserializeConfig.backend_config'_of_string.

Definition erasure_phases_of_string := DeserializeConfig.erasure_phases'_of_string.

Definition attributes_config_of_string := DeserializeConfig.attributes_config_of_string.
