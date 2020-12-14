_(pure Protocol program_protocol ()
  _(reads {})
  _(ensures \result == 
    size(\lambda \integer size; size > 1 && size >= 1, \lambda \integer size; 
      intVal(\lambda \integer x; x >= 0 && x % size == 0,
      \lambda \integer n; 
      intVal(\lambda \integer x; x >= 0 && x > 0,
      \lambda \integer numIterations; 
      foreach(1, numIterations, \lambda \integer iter;
        seq(foreach(1, (size - 1), \lambda \integer pipe;
          foreach(0, (size - 1), \lambda \integer i;
            message(i, i + 1 < size ? i + 1 : 0, floatArrayRefin(\lambda float* _x9; \integer _x9_length; _x9_length == n / size * 4))
          )
        ), 
        allreduce(MPI_MIN, floatArrayRefin(\lambda float* _x11; \integer _x11_length; _x11_length == 1 && \true)))
      )))
    )
  );
)
