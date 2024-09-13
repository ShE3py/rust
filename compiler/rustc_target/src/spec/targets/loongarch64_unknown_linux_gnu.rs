use crate::spec::{base, CodeModel, Target, TargetOptions};

pub(crate) fn target() -> Target {
    Target {
        llvm_target: "loongarch64-unknown-linux-gnu".into(),
        metadata: crate::spec::TargetMetadata {
            description: Some("LoongArch64 Linux, LP64D ABI (kernel 5.19, glibc 2.36)".into()),
            tier: Some(2),
            host_tools: Some(true),
            std: Some(true),
        },
        pointer_width: 64,
        data_layout: "e-m:e-p:64:64-i64:64-i128:128-n32:64-S128".into(),
        arch: "loongarch64".into(),
        options: TargetOptions {
            code_model: Some(CodeModel::Medium),
            cpu: "generic".into(),
            features: "+f,+d".into(),
            llvm_abiname: "lp64d".into(),
            max_atomic_width: Some(64),
            direct_access_external_data: Some(false),
            ..base::linux_gnu::opts()
        },
    }
}
