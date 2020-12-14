_(pure Protocol program_protocol ()
  _(reads {})
  _(ensures \result == 
    size(\lambda \integer size; size >= 2, \lambda \integer size; 
      intBcast(0, \lambda \integer x; x > 0 && x % size == 0,
      \lambda \integer n; 
      seq(foreach(1, (size - 1), \lambda \integer i;
        message(0, i, floatArrayRefin(\lambda float* _x5; \integer _x5_length; _x5_length == n / size))
      ), 
      seq(foreach(1, (size - 1), \lambda \integer i;
        message(0, i, floatArrayRefin(\lambda float* _x10; \integer _x10_length; _x10_length == n / size))
      ), 
      seq(allreduce(MPI_SUM, floatArrayRefin(\lambda float* _x12; \integer _x12_length; _x12_length == 1 && \true)), 
      foreach(1, (size - 1), \lambda \integer i;
        message(i, 0, floatArrayRefin(\lambda float* _x15; \integer _x15_length; _x15_length == 1 && \true))
      )))))
    )
  );
)
