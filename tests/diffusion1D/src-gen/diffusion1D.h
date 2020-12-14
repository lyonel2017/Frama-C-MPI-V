_(pure Protocol program_protocol ()
  _(reads {})
  _(ensures \result == 
    size(\lambda \integer size; size >= 2, \lambda \integer size; 
      intBcast(0, \lambda \integer x; x > 0 && x % size == 0,
      \lambda \integer n; 
      intBcast(0, \lambda \integer _x2; _x2 > 0,
      \lambda \integer numIterations; 
      intBcast(0, \lambda \integer _x5; \true,
      \lambda \integer _x4; 
      seq(foreach(1, (size - 1), \lambda \integer i;
        message(0, i, floatArrayRefin(\lambda float* _x10; \integer _x10_length; _x10_length == n / size))
      ), 
      foreach(1, numIterations, \lambda \integer iter;
        seq(foreach(1, (size - 1), \lambda \integer i;
          message(i, i - 1, floatArrayRefin(\lambda float* _x14; \integer _x14_length; _x14_length == 1 && \true))
        ), 
        foreach(0, (size - 2), \lambda \integer i;
          message(i, i + 1, floatArrayRefin(\lambda float* _x17; \integer _x17_length; _x17_length == 1 && \true))
        ))
      )))))
    )
  );
)
