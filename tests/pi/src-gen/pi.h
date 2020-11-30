_(pure Protocol program_protocol ()
  _(reads {})
  _(ensures \result == 
    size(\lambda \integer _x0; _x0 > 0, \lambda \integer size; 
      intBcast(0, \lambda \integer _x2; \true,
      \lambda \integer _x1; 
      reduce(0, MPI_SUM, floatArrayRefin(\lambda float* _x4; \integer _x4_length; _x4_length == 1 && \true)))
    )
  );
)
