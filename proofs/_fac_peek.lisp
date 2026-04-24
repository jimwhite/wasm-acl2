(in-package "WASM")
(include-book "../execution")
(include-book "wasm-loader")

(make-event
 (mv-let (erp funcs acl2::state)
   (load-wasm-funcinsts "../tests/oracle/factorial.wasm" acl2::state)
   (if erp
       (mv (msg "load failed: ~x0" erp) nil acl2::state)
     (mv nil
         `(progn
            (defconst *fac-func* ',(first funcs))
            (defconst *fac-body* ',(funcinst->body (first funcs))))
         acl2::state))))

(value-triple *fac-body*)
(value-triple (funcinst->param-count *fac-func*))
(value-triple (funcinst->local-count *fac-func*))
(value-triple (funcinst->return-arity *fac-func*))
