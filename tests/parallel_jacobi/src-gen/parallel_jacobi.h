_(pure Protocol program_protocol ()
  _(reads {})
  _(ensures \result == 
    size(\lambda \integer _x0; _x0 > 0, \lambda \integer size; 
      intVal(\lambda \integer y; y > 0 && y % size == 0 && y * y % size == 0,
      \lambda \integer n; 
      intVal(\lambda \integer _x3; \true,
      \lambda \integer maxIter; 
      seq(scatter(0, floatArrayRefin(\lambda float* _x7; \integer _x7_length; _x7_length == n * n)), 
      seq(scatter(0, floatArrayRefin(\lambda float* _x11; \integer _x11_length; _x11_length == n)), 
      seq(allgather(floatArrayRefin(\lambda float* _x15; \integer _x15_length; _x15_length == n / size)), 
      seq(foreach(1, maxIter, \lambda \integer i;
        allgather(floatArrayRefin(\lambda float* _x20; \integer _x20_length; _x20_length == n / size))
      ), 
      gather(0, floatArrayRefin(\lambda float* _x24; \integer _x24_length; _x24_length == n / size))))))))
    )
  );
)
