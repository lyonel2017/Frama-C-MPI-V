#include "mpi.h"

//frama-c-gui -mpi-v -wp-driver ../../share/mpi.driver,the_protocol.driver,size.driver gather_scatter.c

int main(int argc, char **argv){
  int my_rank = 0, num_procs = 0;

  /* Initialize the infrastructure necessary for communication */
  MPI_Init(&argc, &argv);

  /* Identify this process */
  MPI_Comm_rank(MPI_COMM_WORLD, &my_rank);

  /* Find out how many total processes are active */
  MPI_Comm_size(MPI_COMM_WORLD, &num_procs);

  /* Until this point, all programs have been doing exactly the same.
     Here, we check the rank to distinguish the roles of the programs */
  if (my_rank == 0) {
    //int recvdata[num_procs];
    int recvdata[100];
    int senddata = my_rank;
    /* Gather messages for all processes*/
    MPI_Gather(&senddata, 1, MPI_INT,recvdata, 1, MPI_INT,0, MPI_COMM_WORLD);

    /*@ assert \false;*/

    int senddata2[100];
    int recvdata2 = my_rank;
    /* Gather messages for all processes*/
    MPI_Scatter(senddata2, 1, MPI_INT,&recvdata2, 1, MPI_INT,0, MPI_COMM_WORLD);


  } else{
    int senddata = my_rank;
    int* a = 0;
    /* Receive message from process 0 */
    MPI_Gather(&senddata, 1, MPI_INT,a, 1, MPI_INT,0, MPI_COMM_WORLD);
    int* b = 0;
    int recvdata;
    /* Gather messages for all processes*/
     MPI_Scatter(b, 1, MPI_INT,&recvdata, 1, MPI_INT,0, MPI_COMM_WORLD);
  }

  /* Tear down the communication infrastructure */
  MPI_Finalize();
  return 0;
}
