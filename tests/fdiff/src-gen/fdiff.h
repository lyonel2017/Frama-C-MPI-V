_(pure Protocol program_protocol ()
  _(reads {})
  _(ensures \result == 
    size(\lambda \integer size; size > 2 && size >= 1, \lambda \integer size; 
      intVal(\lambda \integer _x0; _x0 > 0,
      \lambda \integer numIterations; 
      intBcast(0, \lambda \integer x; x > 0 && x % size == 0,
      \lambda \integer n; 
      seq(scatter(0, floatArrayRefin(\lambda float* _x6; \integer _x6_length; _x6_length == n)), 
      seq(foreach(1, numIterations, \lambda \integer iteration;
        foreach(0, (size - 1), \lambda \integer i;
          seq(message(i, i == 0 ? size - 1 : i - 1, floatArrayRefin(\lambda float* _x10; \integer _x10_length; _x10_length == 1 && \true)), 
          message(i, i == size - 1 ? 0 : i + 1, floatArrayRefin(\lambda float* _x12; \integer _x12_length; _x12_length == 1 && \true)))
        )
      ), 
      seq(reduce(0, MPI_MAX, floatArrayRefin(\lambda float* _x14; \integer _x14_length; _x14_length == 1 && \true)), 
      gather(0, floatArrayRefin(\lambda float* _x18; \integer _x18_length; _x18_length == n / size)))))))
    )
  );
)
