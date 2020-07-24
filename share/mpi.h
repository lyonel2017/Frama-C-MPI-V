/* ompi/include/mpi.h.  Generated from mpi.h.in by configure.  */
/*
 * Copyright (c) 2004-2005 The Trustees of Indiana University and Indiana
 *                         University Research and Technology
 *                         Corporation.  All rights reserved.
 * Copyright (c) 2004-2013 The University of Tennessee and The University
 *                         of Tennessee Research Foundation.  All rights
 *                         reserved.
 * Copyright (c) 2004-2007 High Performance Computing Center Stuttgart,
 *                         University of Stuttgart.  All rights reserved.
 * Copyright (c) 2004-2005 The Regents of the University of California.
 *                         All rights reserved.
 * Copyright (c) 2007-2016 Cisco Systems, Inc.  All rights reserved.
 * Copyright (c) 2008-2009 Sun Microsystems, Inc.  All rights reserved.
 * Copyright (c) 2009-2012 Oak Rigde National Laboratory.  All rights reserved.
 * Copyright (c) 2011      Sandia National Laboratories. All rights reserved.
 * Copyright (c) 2012-2015 Los Alamos National Security, LLC. All rights
 *                         reserved.
 * Copyright (c) 2011-2013 INRIA.  All rights reserved.
 * Copyright (c) 2015      University of Houston. All rights reserved.
 * Copyright (c) 2015      Research Organization for Information Science
 *                         and Technology (RIST). All rights reserved.
 * Copyright (c) 2017      IBM Corporation.  All rights reserved.
 * $COPYRIGHT$
 *
 * Additional copyrights may follow
 *
 * $HEADER$
 */

#ifndef __FC_MPI
#define __FC_MPI

/*
 * Miscellaneous constants
 */
#define MPI_ANY_SOURCE         -1                      /* match any source rank */
#define MPI_PROC_NULL          -2                      /* rank of null process */
#define MPI_ROOT               -4                      /* special value for intercomms */
#define MPI_ANY_TAG            -1                      /* match any message tag */
#define MPI_MAX_LIBRARY_VERSION_STRING 256             /* max length of library version string */
#define MPI_UNDEFINED          -32766                  /* undefined stuff */
#define MPI_DIST_GRAPH         3                       /* dist graph topology */
#define MPI_CART               1                       /* cartesian topology */
#define MPI_GRAPH              2                       /* graph topology */
#define MPI_KEYVAL_INVALID     -1                      /* invalid key value */

/*
 * More constants
 */
#define MPI_UNWEIGHTED           ((int *) 2)           /* unweighted graph */
#define MPI_WEIGHTS_EMPTY        ((int *) 3)           /* empty weights */
#define MPI_BOTTOM               ((void *) 0)          /* base reference address */
#define MPI_IN_PLACE             ((void *) 1)          /* in place buffer */
#define MPI_BSEND_OVERHEAD       128                   /* size of bsend header + ptr */
#define MPI_ARGV_NULL            ((char **) 0)         /* NULL argument vector */
#define MPI_ARGVS_NULL           ((char ***) 0)        /* NULL argument vectors */
#define MPI_ERRCODES_IGNORE      ((int *) 0)           /* don't return error codes */
#define MPI_ORDER_C              0                     /* C row major order */
#define MPI_ORDER_FORTRAN        1                     /* Fortran column major order */
#define MPI_DISTRIBUTE_BLOCK     0                     /* block distribution */
#define MPI_DISTRIBUTE_CYCLIC    1                     /* cyclic distribution */
#define MPI_DISTRIBUTE_NONE      2                     /* not distributed */
#define MPI_DISTRIBUTE_DFLT_DARG (-1)                  /* default distribution arg */

/*
 * MPI-2 One-Sided Communications asserts
 */
#define MPI_MODE_NOCHECK             1
#define MPI_MODE_NOPRECEDE           2
#define MPI_MODE_NOPUT               4
#define MPI_MODE_NOSTORE             8
#define MPI_MODE_NOSUCCEED          16

#define MPI_LOCK_EXCLUSIVE           1
#define MPI_LOCK_SHARED              2

#define MPI_WIN_FLAVOR_CREATE        1
#define MPI_WIN_FLAVOR_ALLOCATE      2
#define MPI_WIN_FLAVOR_DYNAMIC       3
#define MPI_WIN_FLAVOR_SHARED        4

#define MPI_WIN_UNIFIED              0
#define MPI_WIN_SEPARATE             1

/*
 * Predefined attribute keyvals
 *
 * DO NOT CHANGE THE ORDER WITHOUT ALSO CHANGING THE ORDER IN
 * src/attribute/attribute_predefined.c and mpif.h.in.
 */
enum {
    /* MPI-1 */
    MPI_TAG_UB,
    MPI_HOST,
    MPI_IO,
    MPI_WTIME_IS_GLOBAL,

    /* MPI-2 */
    MPI_APPNUM,
    MPI_LASTUSEDCODE,
    MPI_UNIVERSE_SIZE,
    MPI_WIN_BASE,
    MPI_WIN_SIZE,
    MPI_WIN_DISP_UNIT,
    MPI_WIN_CREATE_FLAVOR,
    MPI_WIN_MODEL,

    /* Even though these four are IMPI attributes, they need to be there
       for all MPI jobs */
    IMPI_CLIENT_SIZE,
    IMPI_CLIENT_COLOR,
    IMPI_HOST_SIZE,
    IMPI_HOST_COLOR
};

/*
 * Error classes and codes
 * Do not change the values of these without also modifying mpif.h.in.
 */
#define MPI_SUCCESS                   0
#define MPI_ERR_BUFFER                1
#define MPI_ERR_COUNT                 2
#define MPI_ERR_TYPE                  3
#define MPI_ERR_TAG                   4
#define MPI_ERR_COMM                  5
#define MPI_ERR_RANK                  6
#define MPI_ERR_REQUEST               7
#define MPI_ERR_ROOT                  8
#define MPI_ERR_GROUP                 9
#define MPI_ERR_OP                    10
#define MPI_ERR_TOPOLOGY              11
#define MPI_ERR_DIMS                  12
#define MPI_ERR_ARG                   13
#define MPI_ERR_UNKNOWN               14
#define MPI_ERR_TRUNCATE              15
#define MPI_ERR_OTHER                 16
#define MPI_ERR_INTERN                17
#define MPI_ERR_IN_STATUS             18
#define MPI_ERR_PENDING               19
#define MPI_ERR_ACCESS                20
#define MPI_ERR_AMODE                 21
#define MPI_ERR_ASSERT                22
#define MPI_ERR_BAD_FILE              23
#define MPI_ERR_BASE                  24
#define MPI_ERR_CONVERSION            25
#define MPI_ERR_DISP                  26
#define MPI_ERR_DUP_DATAREP           27
#define MPI_ERR_FILE_EXISTS           28
#define MPI_ERR_FILE_IN_USE           29
#define MPI_ERR_FILE                  30
#define MPI_ERR_INFO_KEY              31
#define MPI_ERR_INFO_NOKEY            32
#define MPI_ERR_INFO_VALUE            33
#define MPI_ERR_INFO                  34
#define MPI_ERR_IO                    35
#define MPI_ERR_KEYVAL                36
#define MPI_ERR_LOCKTYPE              37
#define MPI_ERR_NAME                  38
#define MPI_ERR_NO_MEM                39
#define MPI_ERR_NOT_SAME              40
#define MPI_ERR_NO_SPACE              41
#define MPI_ERR_NO_SUCH_FILE          42
#define MPI_ERR_PORT                  43
#define MPI_ERR_QUOTA                 44
#define MPI_ERR_READ_ONLY             45
#define MPI_ERR_RMA_CONFLICT          46
#define MPI_ERR_RMA_SYNC              47
#define MPI_ERR_SERVICE               48
#define MPI_ERR_SIZE                  49
#define MPI_ERR_SPAWN                 50
#define MPI_ERR_UNSUPPORTED_DATAREP   51
#define MPI_ERR_UNSUPPORTED_OPERATION 52
#define MPI_ERR_WIN                   53
#define MPI_T_ERR_MEMORY              54
#define MPI_T_ERR_NOT_INITIALIZED     55
#define MPI_T_ERR_CANNOT_INIT         56
#define MPI_T_ERR_INVALID_INDEX       57
#define MPI_T_ERR_INVALID_ITEM        58
#define MPI_T_ERR_INVALID_HANDLE      59
#define MPI_T_ERR_OUT_OF_HANDLES      60
#define MPI_T_ERR_OUT_OF_SESSIONS     61
#define MPI_T_ERR_INVALID_SESSION     62
#define MPI_T_ERR_CVAR_SET_NOT_NOW    63
#define MPI_T_ERR_CVAR_SET_NEVER      64
#define MPI_T_ERR_PVAR_NO_STARTSTOP   65
#define MPI_T_ERR_PVAR_NO_WRITE       66
#define MPI_T_ERR_PVAR_NO_ATOMIC      67
#define MPI_ERR_RMA_RANGE             68
#define MPI_ERR_RMA_ATTACH            69
#define MPI_ERR_RMA_FLAVOR            70
#define MPI_ERR_RMA_SHARED            71
#define MPI_T_ERR_INVALID             72
#define MPI_T_ERR_INVALID_NAME        73

/* Per MPI-3 p349 47, MPI_ERR_LASTCODE must be >= the last predefined
   MPI_ERR_<foo> code. Set the last code to allow some room for adding
   error codes without breaking ABI. */
#define MPI_ERR_LASTCODE              92

/*
 * Comparison results.  Don't change the order of these, the group
 * comparison functions rely on it.
 * Do not change the order of these without also modifying mpif.h.in.
 */
enum {
  MPI_IDENT,
  MPI_CONGRUENT,
  MPI_SIMILAR,
  MPI_UNEQUAL
};

/*
 * MPI_Init_thread constants
 * Do not change the order of these without also modifying mpif.h.in.
 */
enum {
  MPI_THREAD_SINGLE,
  MPI_THREAD_FUNNELED,
  MPI_THREAD_SERIALIZED,
  MPI_THREAD_MULTIPLE
};

/*
 * Datatype combiners.
 * Do not change the order of these without also modifying mpif.h.in.
 * (see also mpif-common.h.fin).
 */
enum {
  MPI_COMBINER_NAMED,
  MPI_COMBINER_DUP,
  MPI_COMBINER_CONTIGUOUS,
  MPI_COMBINER_VECTOR,
  MPI_COMBINER_HVECTOR_INTEGER,
  MPI_COMBINER_HVECTOR,
  MPI_COMBINER_INDEXED,
  MPI_COMBINER_HINDEXED_INTEGER,
  MPI_COMBINER_HINDEXED,
  MPI_COMBINER_INDEXED_BLOCK,
  MPI_COMBINER_STRUCT_INTEGER,
  MPI_COMBINER_STRUCT,
  MPI_COMBINER_SUBARRAY,
  MPI_COMBINER_DARRAY,
  MPI_COMBINER_F90_REAL,
  MPI_COMBINER_F90_COMPLEX,
  MPI_COMBINER_F90_INTEGER,
  MPI_COMBINER_RESIZED,
  MPI_COMBINER_HINDEXED_BLOCK
};

/*
 * Communicator split type constants.
 * Do not change the order of these without also modifying mpif.h.in
 * (see also mpif-common.h.fin).
 */
enum {
  MPI_COMM_TYPE_SHARED,
  OMPI_COMM_TYPE_HWTHREAD,
  OMPI_COMM_TYPE_CORE,
  OMPI_COMM_TYPE_L1CACHE,
  OMPI_COMM_TYPE_L2CACHE,
  OMPI_COMM_TYPE_L3CACHE,
  OMPI_COMM_TYPE_SOCKET,
  OMPI_COMM_TYPE_NUMA,
  OMPI_COMM_TYPE_BOARD,
  OMPI_COMM_TYPE_HOST,
  OMPI_COMM_TYPE_CU,
  OMPI_COMM_TYPE_CLUSTER
};
#define OMPI_COMM_TYPE_NODE MPI_COMM_TYPE_SHARED

/*
 * MPIT Verbosity Levels
 */
enum {
  MPI_T_VERBOSITY_USER_BASIC,
  MPI_T_VERBOSITY_USER_DETAIL,
  MPI_T_VERBOSITY_USER_ALL,
  MPI_T_VERBOSITY_TUNER_BASIC,
  MPI_T_VERBOSITY_TUNER_DETAIL,
  MPI_T_VERBOSITY_TUNER_ALL,
  MPI_T_VERBOSITY_MPIDEV_BASIC,
  MPI_T_VERBOSITY_MPIDEV_DETAIL,
  MPI_T_VERBOSITY_MPIDEV_ALL
};

/*
 * MPIT Scopes
 */
enum {
  MPI_T_SCOPE_CONSTANT,
  MPI_T_SCOPE_READONLY,
  MPI_T_SCOPE_LOCAL,
  MPI_T_SCOPE_GROUP,
  MPI_T_SCOPE_GROUP_EQ,
  MPI_T_SCOPE_ALL,
  MPI_T_SCOPE_ALL_EQ
};

/*
 * MPIT Object Binding
 */
enum {
  MPI_T_BIND_NO_OBJECT,
  MPI_T_BIND_MPI_COMM,
  MPI_T_BIND_MPI_DATATYPE,
  MPI_T_BIND_MPI_ERRHANDLER,
  MPI_T_BIND_MPI_FILE,
  MPI_T_BIND_MPI_GROUP,
  MPI_T_BIND_MPI_OP,
  MPI_T_BIND_MPI_REQUEST,
  MPI_T_BIND_MPI_WIN,
  MPI_T_BIND_MPI_MESSAGE,
  MPI_T_BIND_MPI_INFO
};

/*
 * MPIT pvar classes
 */
enum {
  MPI_T_PVAR_CLASS_STATE,
  MPI_T_PVAR_CLASS_LEVEL,
  MPI_T_PVAR_CLASS_SIZE,
  MPI_T_PVAR_CLASS_PERCENTAGE,
  MPI_T_PVAR_CLASS_HIGHWATERMARK,
  MPI_T_PVAR_CLASS_LOWWATERMARK,
  MPI_T_PVAR_CLASS_COUNTER,
  MPI_T_PVAR_CLASS_AGGREGATE,
  MPI_T_PVAR_CLASS_TIMER,
  MPI_T_PVAR_CLASS_GENERIC
};

/* Type of MPI_Aint */
#define MPI_Aint ptrdiff_t

/* Type of MPI_Offset */
#define MPI_Offset long long

/* Type of MPI_Count */
#define MPI_Count long long

/*
 * Typedefs
 */
typedef struct mpi_communicator_t *MPI_Comm;
typedef struct mpi_datatype_t *MPI_Datatype;
typedef struct mpi_errhandler_t *MPI_Errhandler;
typedef struct mpi_group_t *MPI_Group;
typedef struct mpi_info_t *MPI_Info;
typedef struct mpi_op_t *MPI_Op;
typedef struct mpi_request_t *MPI_Request;
typedef struct mpi_message_t *MPI_Message;
typedef struct mpi_status_public_t MPI_Status;
typedef struct mpi_win_t *MPI_Win;
typedef struct mca_base_var_enum_t *MPI_T_enum;
typedef struct mpi_mpit_cvar_handle_t *MPI_T_cvar_handle;
typedef struct mca_base_pvar_handle_t *MPI_T_pvar_handle;
typedef struct mca_base_pvar_session_t *MPI_T_pvar_session;

/*
 * MPI_Status
 */
struct mpi_status_public_t {
    /* These fields are publicly defined in the MPI specification.
       User applications may freely read from these fields. */
    int MPI_SOURCE;
    int MPI_TAG;
    int MPI_ERROR;
};
typedef struct mpi_status_public_t mpi_status_public_t;


/*
 * External variables
 */
extern struct mpi_communicator_t mpi_mpi_comm_world;
extern struct mpi_communicator_t mpi_mpi_comm_self;
extern struct mpi_communicator_t mpi_mpi_comm_null;

extern struct mpi_group_t mpi_mpi_group_empty;
extern struct mpi_group_t mpi_mpi_group_null;

extern struct mpi_request_t mpi_request_null;

extern struct mpi_message_t mpi_message_null;
extern struct mpi_message_t mpi_message_no_proc;

extern struct mpi_op_t mpi_mpi_op_null;
extern struct mpi_op_t mpi_mpi_op_min;
extern struct mpi_op_t mpi_mpi_op_max;
extern struct mpi_op_t mpi_mpi_op_sum;
extern struct mpi_op_t mpi_mpi_op_prod;
extern struct mpi_op_t mpi_mpi_op_land;
extern struct mpi_op_t mpi_mpi_op_band;
extern struct mpi_op_t mpi_mpi_op_lor;
extern struct mpi_op_t mpi_mpi_op_bor;
extern struct mpi_op_t mpi_mpi_op_lxor;
extern struct mpi_op_t mpi_mpi_op_bxor;
extern struct mpi_op_t mpi_mpi_op_maxloc;
extern struct mpi_op_t mpi_mpi_op_minloc;
extern struct mpi_op_t mpi_mpi_op_replace;
extern struct mpi_op_t mpi_mpi_op_no_op;


extern struct mpi_datatype_t mpi_mpi_char;
extern struct mpi_datatype_t mpi_mpi_signed_char;
extern struct mpi_datatype_t mpi_mpi_unsigned_char;
extern struct mpi_datatype_t mpi_mpi_short;
extern struct mpi_datatype_t mpi_mpi_unsigned_short;
extern struct mpi_datatype_t mpi_mpi_int;
extern struct mpi_datatype_t mpi_mpi_unsigned;
extern struct mpi_datatype_t mpi_mpi_long;
extern struct mpi_datatype_t mpi_mpi_unsigned_long;
extern struct mpi_datatype_t mpi_mpi_long_long_int;
extern struct mpi_datatype_t mpi_mpi_unsigned_long_long;
extern struct mpi_datatype_t mpi_mpi_float;
extern struct mpi_datatype_t mpi_mpi_double;
extern struct mpi_datatype_t mpi_mpi_long_double;


#define MPI_PREDEFINED_GLOBAL(type, global) (&(global))

/*
 * NULL handles
 */
#define MPI_GROUP_NULL MPI_PREDEFINED_GLOBAL(MPI_Group, mpi_mpi_group_null)
#define MPI_COMM_NULL MPI_PREDEFINED_GLOBAL(MPI_Comm, mpi_mpi_comm_null)
#define MPI_REQUEST_NULL MPI_PREDEFINED_GLOBAL(MPI_Request, mpi_request_null)
#define MPI_MESSAGE_NULL MPI_PREDEFINED_GLOBAL(MPI_Message, mpi_message_null)
#define MPI_OP_NULL MPI_PREDEFINED_GLOBAL(MPI_Op, mpi_mpi_op_null)
#define MPI_T_ENUM_NULL ((MPI_T_enum) NULL)

/*
 * MPI_INFO_ENV handle
 */
#define MPI_STATUS_IGNORE ((MPI_Status *) 0)
#define MPI_STATUSES_IGNORE ((MPI_Status *) 0)

/*
 * MPI predefined handles
 */
#define MPI_COMM_WORLD MPI_PREDEFINED_GLOBAL(MPI_Comm, mpi_mpi_comm_world)
#define MPI_COMM_SELF MPI_PREDEFINED_GLOBAL(MPI_Comm, mpi_mpi_comm_self)

#define MPI_GROUP_EMPTY MPI_PREDEFINED_GLOBAL(MPI_Group, mpi_mpi_group_empty)

#define MPI_MESSAGE_NO_PROC MPI_PREDEFINED_GLOBAL(MPI_Message, mpi_message_no_proc)

#define MPI_MAX MPI_PREDEFINED_GLOBAL(MPI_Op, mpi_mpi_op_max)
#define MPI_MIN MPI_PREDEFINED_GLOBAL(MPI_Op, mpi_mpi_op_min)
#define MPI_SUM MPI_PREDEFINED_GLOBAL(MPI_Op, mpi_mpi_op_sum)
#define MPI_PROD MPI_PREDEFINED_GLOBAL(MPI_Op, mpi_mpi_op_prod)
#define MPI_LAND MPI_PREDEFINED_GLOBAL(MPI_Op, mpi_mpi_op_land)
#define MPI_BAND MPI_PREDEFINED_GLOBAL(MPI_Op, mpi_mpi_op_band)
#define MPI_LOR MPI_PREDEFINED_GLOBAL(MPI_Op, mpi_mpi_op_lor)
#define MPI_BOR MPI_PREDEFINED_GLOBAL(MPI_Op, mpi_mpi_op_bor)
#define MPI_LXOR MPI_PREDEFINED_GLOBAL(MPI_Op, mpi_mpi_op_lxor)
#define MPI_BXOR MPI_PREDEFINED_GLOBAL(MPI_Op, mpi_mpi_op_bxor)
#define MPI_MAXLOC MPI_PREDEFINED_GLOBAL(MPI_Op, mpi_mpi_op_maxloc)
#define MPI_MINLOC MPI_PREDEFINED_GLOBAL(MPI_Op, mpi_mpi_op_minloc)
#define MPI_REPLACE MPI_PREDEFINED_GLOBAL(MPI_Op, mpi_mpi_op_replace)
#define MPI_NO_OP MPI_PREDEFINED_GLOBAL(MPI_Op, mpi_mpi_op_no_op)

/* C datatypes */
#define MPI_CHAR MPI_PREDEFINED_GLOBAL(MPI_Datatype, mpi_mpi_char)
#define MPI_SHORT MPI_PREDEFINED_GLOBAL(MPI_Datatype, mpi_mpi_short)
#define MPI_INT MPI_PREDEFINED_GLOBAL(MPI_Datatype, mpi_mpi_int)
#define MPI_LONG MPI_PREDEFINED_GLOBAL(MPI_Datatype, mpi_mpi_long)
#define MPI_FLOAT MPI_PREDEFINED_GLOBAL(MPI_Datatype, mpi_mpi_float)
#define MPI_DOUBLE MPI_PREDEFINED_GLOBAL(MPI_Datatype, mpi_mpi_double)
#define MPI_LONG_DOUBLE MPI_PREDEFINED_GLOBAL(MPI_Datatype, mpi_mpi_long_double)
#define MPI_UNSIGNED_CHAR MPI_PREDEFINED_GLOBAL(MPI_Datatype, mpi_mpi_unsigned_char)
#define MPI_SIGNED_CHAR MPI_PREDEFINED_GLOBAL(MPI_Datatype, mpi_mpi_signed_char)
#define MPI_UNSIGNED_SHORT MPI_PREDEFINED_GLOBAL(MPI_Datatype, mpi_mpi_unsigned_short)
#define MPI_UNSIGNED_LONG MPI_PREDEFINED_GLOBAL(MPI_Datatype, mpi_mpi_unsigned_long)
#define MPI_UNSIGNED MPI_PREDEFINED_GLOBAL(MPI_Datatype, mpi_mpi_unsigned)
#define MPI_SHORT_INT MPI_PREDEFINED_GLOBAL(MPI_Datatype, mpi_mpi_short_int)
#define MPI_LONG_LONG_INT MPI_PREDEFINED_GLOBAL(MPI_Datatype, mpi_mpi_long_long_int)
#define MPI_LONG_LONG MPI_PREDEFINED_GLOBAL(MPI_Datatype, mpi_mpi_long_long_int)
#define MPI_UNSIGNED_LONG_LONG MPI_PREDEFINED_GLOBAL(MPI_Datatype, mpi_mpi_unsigned_long_long)

/* Typeclass definition for MPI_Type_match_size */
#define MPI_TYPECLASS_INTEGER    1
#define MPI_TYPECLASS_REAL       2
#define MPI_TYPECLASS_COMPLEX    3

/* Aint helper macros (MPI-3.1) */
#define MPI_Aint_add(base, disp) ((MPI_Aint) ((char *) (base) + (disp)))
#define MPI_Aint_diff(addr1, addr2) ((MPI_Aint) ((char *) (addr1) - (char *) (addr2)))
#define PMPI_Aint_add(base, disp) MPI_Aint_add(base, disp)
#define PMPI_Aint_diff(addr1, addr2) MPI_Aint_diff(addr1, addr2)

/*
 * MPI API
 */

/*@ ghost int __MPI_COMM_WORLD_size_ACSL;*/
/*@ ghost int __MPI_COMM_WORLD_rank_ACSL;*/


/*@ ensures 0 <= __MPI_COMM_WORLD_rank_ACSL < __MPI_COMM_WORLD_size_ACSL;
  @ // generated by tool : maybe we want to proof for a limited world size
  @ ensures  __MPI_COMM_WORLD_size_ACSL == 20;
  @ assigns __MPI_COMM_WORLD_size_ACSL,__MPI_COMM_WORLD_rank_ACSL;*/
int MPI_Init(int *argc, char ***argv);


/*@ requires \valid(rank);
  @ requires comm == MPI_COMM_WORLD;
  @ ensures __MPI_COMM_WORLD_rank_ACSL == *rank;
  @ assigns *rank,\result;*/
int MPI_Comm_rank(MPI_Comm comm, int *rank);


/*@ requires \valid(size);
  @ requires comm == MPI_COMM_WORLD;
  @ ensures __MPI_COMM_WORLD_size_ACSL == *size;
  @ assigns *size;*/
int MPI_Comm_size(MPI_Comm comm, int *size);

/*@ assigns \result;*/
int MPI_Finalize(void);



/*@ predicate empty_block_int{L}(int *s) =
  @   \block_length((int*)s) == 0 && \offset((int*)s) == 0;
  @ predicate valid_read_or_empty_int{L}(int *s, int n) =
  @   (empty_block_int(s) && n == 0) || \valid_read(((int*)s)+(0..n-1));
  @ predicate non_escaping_int{L}(int *s, int n) =
  @   \forall  integer i; 0 ≤ i < n ⇒ ¬\dangling((int*)s + i);*/

/*@ predicate empty_block_char{L}(char *s) =
  @   \block_length((char*)s) == 0 && \offset((char*)s) == 0;
  @ predicate valid_read_or_empty_char{L}(char *s, int n) =
  @   (empty_block_char(s) && n == 0) || \valid_read(((char*)s)+(0..n-1));
  @ predicate non_escaping_char{L}(char *s, int n) =
  @   \forall  integer i; 0 ≤ i < n ⇒ ¬\dangling((char*)s + i);*/

/*@ requires comm == MPI_COMM_WORLD;
  @ requires 0 <= dest < __MPI_COMM_WORLD_size_ACSL;
  @ requires 0 <= count;
  @ requires datatype == MPI_CHAR || datatype == MPI_INT;
  @ assigns \result;
  @ behavior type_int :
  @   assumes datatype == MPI_INT;
  @   requires valid_buf: valid_read_or_empty_int((int *)buf, count);
  @  // requires initialization_buf: \initialized((int *)buf + (0 .. count - 1));
  @  // requires danglingness_buf: non_escaping_int((int *)buf, count);
  @ behavior type_char :
  @   assumes datatype == MPI_CHAR;
  @   requires valid_buf: valid_read_or_empty_char((char *)buf, count);
  @  // requires initialization_buf: \initialized((char *)buf + (0 .. count - 1));
  @  // requires danglingness_buf: non_escaping_char((char *)buf, count);
*/
int MPI_Ssend(const void *buf, int count, MPI_Datatype datatype, int dest, int tag, MPI_Comm comm);


/*@ predicate valid_or_empty_int{L}(int *s, int n) =
  @   (empty_block_int(s) && n == 0) || \valid(((int*)s)+(0..n-1));*/

/*@ predicate valid_or_empty_char{L}(char *s, int n) =
  @   (empty_block_char(s) && n == 0) || \valid(((char*)s)+(0..n-1));*/

/*@ requires comm == MPI_COMM_WORLD;
  @ requires 0 <= source < __MPI_COMM_WORLD_size_ACSL;
  @ requires positive_count: 0 <= count;
  @ requires datatype == MPI_CHAR || datatype == MPI_INT;
  @ requires status == MPI_STATUS_IGNORE;
  @ assigns \result;
  @ behavior type_int :
  @   assumes datatype == MPI_INT;
  @   requires valid_buf: valid_or_empty_int((int *)buf, count);
  @  // requires danglingness_buf: non_escaping_int((int *)buf, count);
  @   assigns ((int *)buf)[0..count-1];
  @ behavior type_char :
  @   assumes datatype == MPI_CHAR;
  @   requires valid_buf: valid_or_empty_char((char *)buf, count);
  @  // requires danglingness_buf: non_escaping_char((char *)buf, count);
  @   assigns ((char *)buf)[0..count-1];
*/
int MPI_Recv(void* buf, int count, MPI_Datatype datatype,
	     int source, int tag, MPI_Comm comm, MPI_Status* status);








/*  int MPI_Abort(MPI_Comm comm, int errorcode); */
/*  int MPI_Accumulate(const void *origin_addr, int origin_count, MPI_Datatype origin_datatype, */
/*                                   int target_rank, MPI_Aint target_disp, int target_count, */
/*                                   MPI_Datatype target_datatype, MPI_Op op, MPI_Win win); */
/*  int MPI_Add_error_class(int *errorclass); */
/*  int MPI_Add_error_code(int errorclass, int *errorcode); */
/*  int MPI_Add_error_string(int errorcode, const char *string); */
/*  int MPI_Allgather(const void *sendbuf, int sendcount, MPI_Datatype sendtype, */
/*                                  void *recvbuf, int recvcount, */
/*                                  MPI_Datatype recvtype, MPI_Comm comm); */
/*  int MPI_Iallgather(const void *sendbuf, int sendcount, MPI_Datatype sendtype, */
/*                                  void *recvbuf, int recvcount, */
/*                                  MPI_Datatype recvtype, MPI_Comm comm, MPI_Request *request); */
/*  int MPI_Allgatherv(const void *sendbuf, int sendcount, MPI_Datatype sendtype, */
/*                                   void *recvbuf, const int recvcounts[], */
/*                                   const int displs[], MPI_Datatype recvtype, MPI_Comm comm); */
/*  int MPI_Iallgatherv(const void *sendbuf, int sendcount, MPI_Datatype sendtype, */
/*                                   void *recvbuf, const int recvcounts[], */
/*                                   const int displs[], MPI_Datatype recvtype, MPI_Comm comm, MPI_Request *request); */
/*  int MPI_Alloc_mem(MPI_Aint size, MPI_Info info, */
/*                                  void *baseptr); */
/*  int MPI_Allreduce(const void *sendbuf, void *recvbuf, int count, */
/*                                  MPI_Datatype datatype, MPI_Op op, MPI_Comm comm); */
/*  int MPI_Iallreduce(const void *sendbuf, void *recvbuf, int count, */
/*                                  MPI_Datatype datatype, MPI_Op op, MPI_Comm comm, MPI_Request *request); */
/*  int MPI_Alltoall(const void *sendbuf, int sendcount, MPI_Datatype sendtype, */
/*                                 void *recvbuf, int recvcount, */
/*                                 MPI_Datatype recvtype, MPI_Comm comm); */
/*  int MPI_Ialltoall(const void *sendbuf, int sendcount, MPI_Datatype sendtype, */
/*                                 void *recvbuf, int recvcount, */
/*                                 MPI_Datatype recvtype, MPI_Comm comm, MPI_Request *request); */
/*  int MPI_Alltoallv(const void *sendbuf, const int sendcounts[], const int sdispls[], */
/*                                  MPI_Datatype sendtype, void *recvbuf, const int recvcounts[], */
/*                                  const int rdispls[], MPI_Datatype recvtype, MPI_Comm comm); */
/*  int MPI_Ialltoallv(const void *sendbuf, const int sendcounts[], const int sdispls[], */
/*                                  MPI_Datatype sendtype, void *recvbuf, const int recvcounts[], */
/*                                  const int rdispls[], MPI_Datatype recvtype, MPI_Comm comm, MPI_Request *request); */
/*  int MPI_Alltoallw(const void *sendbuf, const int sendcounts[], const int sdispls[], const MPI_Datatype sendtypes[], */
/*                                  void *recvbuf, const int recvcounts[], const int rdispls[], const MPI_Datatype recvtypes[], */
/*                                  MPI_Comm comm); */
/*  int MPI_Ialltoallw(const void *sendbuf, const int sendcounts[], const int sdispls[], const MPI_Datatype sendtypes[], */
/*                                  void *recvbuf, const int recvcounts[], const int rdispls[], const MPI_Datatype recvtypes[], */
/*                                  MPI_Comm comm, MPI_Request *request); */
/*  int MPI_Barrier(MPI_Comm comm); */
/*  int MPI_Ibarrier(MPI_Comm comm, MPI_Request *request); */
/*  int MPI_Bcast(void *buffer, int count, MPI_Datatype datatype, */
/*                              int root, MPI_Comm comm); */
/*  int MPI_Bsend(const void *buf, int count, MPI_Datatype datatype, */
/*                              int dest, int tag, MPI_Comm comm); */
/*  int MPI_Ibcast(void *buffer, int count, MPI_Datatype datatype, */
/* 				                              int root, MPI_Comm comm, */
/* 											  MPI_Request *request); */
/*  int MPI_Bsend_init(const void *buf, int count, MPI_Datatype datatype, */
/*                                   int dest, int tag, MPI_Comm comm, MPI_Request *request); */
/*  int MPI_Buffer_attach(void *buffer, int size); */
/*  int MPI_Buffer_detach(void *buffer, int *size); */
/*  int MPI_Cancel(MPI_Request *request); */
/*  int MPI_Cart_coords(MPI_Comm comm, int rank, int maxdims, int coords[]); */
/*  int MPI_Cart_create(MPI_Comm old_comm, int ndims, const int dims[], */
/*                                    const int periods[], int reorder, MPI_Comm *comm_cart); */
/*  int MPI_Cart_get(MPI_Comm comm, int maxdims, int dims[], */
/*                                 int periods[], int coords[]); */
/*  int MPI_Cart_map(MPI_Comm comm, int ndims, const int dims[], */
/*                                 const int periods[], int *newrank); */
/*  int MPI_Cart_rank(MPI_Comm comm, const int coords[], int *rank); */
/*  int MPI_Cart_shift(MPI_Comm comm, int direction, int disp, */
/*                                   int *rank_source, int *rank_dest); */
/*  int MPI_Cart_sub(MPI_Comm comm, const int remain_dims[], MPI_Comm *new_comm); */
/*  int MPI_Cartdim_get(MPI_Comm comm, int *ndims); */
/*  int MPI_Close_port(const char *port_name); */
/*  int MPI_Comm_accept(const char *port_name, MPI_Info info, int root, */
/*                                    MPI_Comm comm, MPI_Comm *newcomm); */
/*  int MPI_Comm_call_errhandler(MPI_Comm comm, int errorcode); */
/*  int MPI_Comm_compare(MPI_Comm comm1, MPI_Comm comm2, int *result); */
/*  int MPI_Comm_connect(const char *port_name, MPI_Info info, int root, */
/*                                     MPI_Comm comm, MPI_Comm *newcomm); */
/*  int MPI_Comm_create_group(MPI_Comm comm, MPI_Group group, int tag, MPI_Comm *newcomm); */
/*  int MPI_Comm_create(MPI_Comm comm, MPI_Group group, MPI_Comm *newcomm); */
/*  int MPI_Comm_delete_attr(MPI_Comm comm, int comm_keyval); */
/*  int MPI_Comm_disconnect(MPI_Comm *comm); */
/*  int MPI_Comm_dup(MPI_Comm comm, MPI_Comm *newcomm); */
/*  int MPI_Comm_idup(MPI_Comm comm, MPI_Comm *newcomm, MPI_Request *request); */
/*  int MPI_Comm_dup_with_info(MPI_Comm comm, MPI_Info info, MPI_Comm *newcomm); */
/*  int MPI_Comm_free_keyval(int *comm_keyval); */
/*  int MPI_Comm_free(MPI_Comm *comm); */
/*  int MPI_Comm_get_attr(MPI_Comm comm, int comm_keyval, */
/*                                      void *attribute_val, int *flag); */
/*  int MPI_Dist_graph_create(MPI_Comm comm_old, int n, const int nodes[], */
/*                                          const int degrees[], const int targets[], */
/*                                          const int weights[], MPI_Info info, */
/*                                          int reorder, MPI_Comm * newcomm); */
/*  int MPI_Dist_graph_create_adjacent(MPI_Comm comm_old, */
/*                                                   int indegree, const int sources[], */
/*                                                   const int sourceweights[], */
/*                                                   int outdegree, */
/*                                                   const int destinations[], */
/*                                                   const int destweights[], */
/*                                                   MPI_Info info, int reorder, */
/*                                                   MPI_Comm *comm_dist_graph); */
/* int MPI_Dist_graph_neighbors(MPI_Comm comm, int maxindegree, */
/*                                            int sources[], int sourceweights[], */
/*                                            int maxoutdegree, */
/*                                            int destinations[], */
/*                                            int destweights[]); */
/*  int MPI_Dist_graph_neighbors_count(MPI_Comm comm, */
/*                                                   int *inneighbors, */
/*                                                   int *outneighbors, */
/*                                                   int *weighted); */
/*  int MPI_Comm_get_errhandler(MPI_Comm comm, MPI_Errhandler *erhandler); */
/*  int MPI_Comm_get_info(MPI_Comm comm, MPI_Info *info_used); */
/*  int MPI_Comm_get_name(MPI_Comm comm, char *comm_name, int *resultlen); */
/*  int MPI_Comm_get_parent(MPI_Comm *parent); */
/*  int MPI_Comm_group(MPI_Comm comm, MPI_Group *group); */
/*  int MPI_Comm_join(int fd, MPI_Comm *intercomm); */
/*  int MPI_Comm_remote_group(MPI_Comm comm, MPI_Group *group); */
/*  int MPI_Comm_remote_size(MPI_Comm comm, int *size); */
/*  int MPI_Comm_set_attr(MPI_Comm comm, int comm_keyval, void *attribute_val); */
/*  int MPI_Comm_set_errhandler(MPI_Comm comm, MPI_Errhandler errhandler); */
/*  int MPI_Comm_set_info(MPI_Comm comm, MPI_Info info); */
/*  int MPI_Comm_set_name(MPI_Comm comm, const char *comm_name); */
/*  int MPI_Comm_spawn(const char *command, char *argv[], int maxprocs, MPI_Info info, */
/*                                   int root, MPI_Comm comm, MPI_Comm *intercomm, */
/*                                   int array_of_errcodes[]); */
/*  int MPI_Comm_spawn_multiple(int count, char *array_of_commands[], char **array_of_argv[], */
/*                                            const int array_of_maxprocs[], const MPI_Info array_of_info[], */
/*                                            int root, MPI_Comm comm, MPI_Comm *intercomm, */
/*                                            int array_of_errcodes[]); */
/*  int MPI_Comm_split(MPI_Comm comm, int color, int key, MPI_Comm *newcomm); */
/*  int MPI_Comm_split_type(MPI_Comm comm, int split_type, int key, MPI_Info info, MPI_Comm *newcomm); */
/*  int MPI_Comm_test_inter(MPI_Comm comm, int *flag); */
/*  int MPI_Compare_and_swap(const void *origin_addr, const void *compare_addr, */
/*                                         void *result_addr, MPI_Datatype datatype, int target_rank, */
/*                                         MPI_Aint target_disp, MPI_Win win); */
/*  int MPI_Dims_create(int nnodes, int ndims, int dims[]); */
/*  int MPI_Errhandler_free(MPI_Errhandler *errhandler); */
/*  int MPI_Error_class(int errorcode, int *errorclass); */
/*  int MPI_Error_string(int errorcode, char *string, int *resultlen); */
/*  int MPI_Exscan(const void *sendbuf, void *recvbuf, int count, */
/*                               MPI_Datatype datatype, MPI_Op op, MPI_Comm comm); */
/*  int MPI_Fetch_and_op(const void *origin_addr, void *result_addr, MPI_Datatype datatype, */
/*                                     int target_rank, MPI_Aint target_disp, MPI_Op op, MPI_Win win); */
/*  int MPI_Iexscan(const void *sendbuf, void *recvbuf, int count, */
/*                               MPI_Datatype datatype, MPI_Op op, MPI_Comm comm, MPI_Request *request); */
/*  int MPI_Finalized(int *flag); */
/*  int MPI_Free_mem(void *base); */
/*  int MPI_Gather(const void *sendbuf, int sendcount, MPI_Datatype sendtype, */
/*                               void *recvbuf, int recvcount, MPI_Datatype recvtype, */
/*                               int root, MPI_Comm comm); */
/*  int MPI_Igather(const void *sendbuf, int sendcount, MPI_Datatype sendtype, */
/*                               void *recvbuf, int recvcount, MPI_Datatype recvtype, */
/*                               int root, MPI_Comm comm, MPI_Request *request); */
/*  int MPI_Gatherv(const void *sendbuf, int sendcount, MPI_Datatype sendtype, */
/*                                void *recvbuf, const int recvcounts[], const int displs[], */
/*                                MPI_Datatype recvtype, int root, MPI_Comm comm); */
/*  int MPI_Igatherv(const void *sendbuf, int sendcount, MPI_Datatype sendtype, */
/*                                void *recvbuf, const int recvcounts[], const int displs[], */
/*                                MPI_Datatype recvtype, int root, MPI_Comm comm, MPI_Request *request); */
/*  int MPI_Get_address(const void *location, MPI_Aint *address); */
/*  int MPI_Get_count(const MPI_Status *status, MPI_Datatype datatype, int *count); */
/*  int MPI_Get_elements(const MPI_Status *status, MPI_Datatype datatype, int *count); */
/*  int MPI_Get_elements_x(const MPI_Status *status, MPI_Datatype datatype, MPI_Count *count); */
/*  int MPI_Get(void *origin_addr, int origin_count, */
/*                            MPI_Datatype origin_datatype, int target_rank, */
/*                            MPI_Aint target_disp, int target_count, */
/*                            MPI_Datatype target_datatype, MPI_Win win); */
/*  int MPI_Get_accumulate(const void *origin_addr, int origin_count, MPI_Datatype origin_datatype, */
/*                                       void *result_addr, int result_count, MPI_Datatype result_datatype, */
/*                                       int target_rank, MPI_Aint target_disp, int target_count, */
/*                                       MPI_Datatype target_datatype, MPI_Op op, MPI_Win win); */
/*  int MPI_Get_library_version(char *version, int *resultlen); */
/*  int MPI_Get_processor_name(char *name, int *resultlen); */
/*  int MPI_Get_version(int *version, int *subversion); */
/*  int MPI_Graph_create(MPI_Comm comm_old, int nnodes, const int index[], */
/*                                     const int edges[], int reorder, MPI_Comm *comm_graph); */
/*  int MPI_Graph_get(MPI_Comm comm, int maxindex, int maxedges, */
/*                                  int index[], int edges[]); */
/*  int MPI_Graph_map(MPI_Comm comm, int nnodes, const int index[], const int edges[], */
/*                                  int *newrank); */
/*  int MPI_Graph_neighbors_count(MPI_Comm comm, int rank, int *nneighbors); */
/*  int MPI_Graph_neighbors(MPI_Comm comm, int rank, int maxneighbors, */
/*                                        int neighbors[]); */
/*  int MPI_Graphdims_get(MPI_Comm comm, int *nnodes, int *nedges); */
/*  int MPI_Grequest_complete(MPI_Request request); */
/*  int MPI_Grequest_start(MPI_Grequest_query_function *query_fn, */
/*                                       MPI_Grequest_free_function *free_fn, */
/*                                       MPI_Grequest_cancel_function *cancel_fn, */
/*                                       void *extra_state, MPI_Request *request); */
/*  int MPI_Group_compare(MPI_Group group1, MPI_Group group2, int *result); */
/*  int MPI_Group_difference(MPI_Group group1, MPI_Group group2, */
/*                                         MPI_Group *newgroup); */
/*  int MPI_Group_excl(MPI_Group group, int n, const int ranks[], */
/*                                   MPI_Group *newgroup); */
/*  int MPI_Group_free(MPI_Group *group); */
/*  int MPI_Group_incl(MPI_Group group, int n, const int ranks[], */
/*                                   MPI_Group *newgroup); */
/*  int MPI_Group_intersection(MPI_Group group1, MPI_Group group2, */
/*                                           MPI_Group *newgroup); */
/*  int MPI_Group_range_excl(MPI_Group group, int n, int ranges[][3], */
/*                                         MPI_Group *newgroup); */
/*  int MPI_Group_range_incl(MPI_Group group, int n, int ranges[][3], */
/*                                         MPI_Group *newgroup); */
/*  int MPI_Group_rank(MPI_Group group, int *rank); */
/*  int MPI_Group_size(MPI_Group group, int *size); */
/*  int MPI_Group_translate_ranks(MPI_Group group1, int n, const int ranks1[], */
/*                                              MPI_Group group2, int ranks2[]); */
/*  int MPI_Group_union(MPI_Group group1, MPI_Group group2, */
/*                                    MPI_Group *newgroup); */
/*  int MPI_Ibsend(const void *buf, int count, MPI_Datatype datatype, int dest, */
/*                               int tag, MPI_Comm comm, MPI_Request *request); */
/*  int MPI_Improbe(int source, int tag, MPI_Comm comm, */
/*                                int *flag, MPI_Message *message, */
/*                                MPI_Status *status); */
/*  int MPI_Imrecv(void *buf, int count, MPI_Datatype type, */
/*                               MPI_Message *message, MPI_Request *request); */
/*  int MPI_Info_create(MPI_Info *info); */
/*  int MPI_Info_delete(MPI_Info info, const char *key); */
/*  int MPI_Info_dup(MPI_Info info, MPI_Info *newinfo); */
/*  int MPI_Info_free(MPI_Info *info); */
/*  int MPI_Info_get(MPI_Info info, const char *key, int valuelen, */
/*                                 char *value, int *flag); */
/*  int MPI_Info_get_nkeys(MPI_Info info, int *nkeys); */
/*  int MPI_Info_get_nthkey(MPI_Info info, int n, char *key); */
/*  int MPI_Info_get_valuelen(MPI_Info info, const char *key, int *valuelen, */
/*                                          int *flag); */
/*  int MPI_Info_set(MPI_Info info, const char *key, const char *value); */
/*  int MPI_Initialized(int *flag); */
/*  int MPI_Init_thread(int *argc, char ***argv, int required, */
/*                                    int *provided); */
/*  int MPI_Intercomm_create(MPI_Comm local_comm, int local_leader, */
/*                                         MPI_Comm bridge_comm, int remote_leader, */
/*                                         int tag, MPI_Comm *newintercomm); */
/*  int MPI_Intercomm_merge(MPI_Comm intercomm, int high, */
/*                                        MPI_Comm *newintercomm); */
/*  int MPI_Iprobe(int source, int tag, MPI_Comm comm, int *flag, */
/*                               MPI_Status *status); */
/*  int MPI_Irecv(void *buf, int count, MPI_Datatype datatype, int source, */
/*                              int tag, MPI_Comm comm, MPI_Request *request); */
/*  int MPI_Irsend(const void *buf, int count, MPI_Datatype datatype, int dest, */
/*                               int tag, MPI_Comm comm, MPI_Request *request); */
/*  int MPI_Isend(const void *buf, int count, MPI_Datatype datatype, int dest, */
/*                              int tag, MPI_Comm comm, MPI_Request *request); */
/*  int MPI_Issend(const void *buf, int count, MPI_Datatype datatype, int dest, */
/*                               int tag, MPI_Comm comm, MPI_Request *request); */
/*  int MPI_Is_thread_main(int *flag); */
/*  int MPI_Lookup_name(const char *service_name, MPI_Info info, char *port_name); */
/*  int MPI_Mprobe(int source, int tag, MPI_Comm comm, */
/*                                MPI_Message *message, */
/*                                MPI_Status *status); */
/*  int MPI_Mrecv(void *buf, int count, MPI_Datatype type, */
/*                              MPI_Message *message, MPI_Status *status); */
/*  int MPI_Neighbor_allgather(const void *sendbuf, int sendcount, MPI_Datatype sendtype, */
/*                                           void *recvbuf, int recvcount, MPI_Datatype recvtype, */
/*                                           MPI_Comm comm); */
/*  int MPI_Ineighbor_allgather(const void *sendbuf, int sendcount, MPI_Datatype sendtype, */
/*                                            void *recvbuf, int recvcount, MPI_Datatype recvtype, */
/*                                            MPI_Comm comm, MPI_Request *request); */
/*  int MPI_Neighbor_allgatherv(const void *sendbuf, int sendcount, MPI_Datatype sendtype, */
/*                                            void *recvbuf, const int recvcounts[], const int displs[], */
/*                                            MPI_Datatype recvtype, MPI_Comm comm); */
/*  int MPI_Ineighbor_allgatherv(const void *sendbuf, int sendcount, MPI_Datatype sendtype, */
/*                                             void *recvbuf, const int recvcounts[], const int displs[], */
/*                                             MPI_Datatype recvtype, MPI_Comm comm, MPI_Request *request); */
/*  int MPI_Neighbor_alltoall(const void *sendbuf, int sendcount, MPI_Datatype sendtype, */
/*                                          void *recvbuf, int recvcount, MPI_Datatype recvtype, */
/*                                          MPI_Comm comm); */
/*  int MPI_Ineighbor_alltoall(const void *sendbuf, int sendcount, MPI_Datatype sendtype, */
/*                                           void *recvbuf, int recvcount, MPI_Datatype recvtype, */
/*                                           MPI_Comm comm, MPI_Request *request); */
/*  int MPI_Neighbor_alltoallv(const void *sendbuf, const int sendcounts[], const int sdispls[],  MPI_Datatype sendtype, */
/*                                           void *recvbuf, const int recvcounts[], const int rdispls[], MPI_Datatype recvtype, */
/*                                           MPI_Comm comm); */
/*  int MPI_Ineighbor_alltoallv(const void *sendbuf, const int sendcounts[], const int sdispls[], MPI_Datatype sendtype, */
/*                                            void *recvbuf, const int recvcounts[], const int rdispls[], MPI_Datatype recvtype, */
/*                                            MPI_Comm comm, MPI_Request *request); */
/*  int MPI_Neighbor_alltoallw(const void *sendbuf, const int sendcounts[], const MPI_Aint sdispls[], const MPI_Datatype sendtypes[], */
/*                                           void *recvbuf, const int recvcounts[], const MPI_Aint rdispls[], const MPI_Datatype recvtypes[], */
/*                                           MPI_Comm comm); */
/*  int MPI_Ineighbor_alltoallw(const void *sendbuf, const int sendcounts[], const MPI_Aint sdispls[], const MPI_Datatype sendtypes[], */
/*                                            void *recvbuf, const int recvcounts[], const MPI_Aint rdispls[], const MPI_Datatype recvtypes[], */
/*                                            MPI_Comm comm, MPI_Request *request); */
/*  int MPI_Op_commutative(MPI_Op op, int *commute); */
/*  int MPI_Op_create(MPI_User_function *function, int commute, MPI_Op *op); */
/*  int MPI_Open_port(MPI_Info info, char *port_name); */
/*  int MPI_Op_free(MPI_Op *op); */
/*  int MPI_Pack_external(const char datarep[], const void *inbuf, int incount, */
/*                                      MPI_Datatype datatype, void *outbuf, */
/*                                      MPI_Aint outsize, MPI_Aint *position); */
/*  int MPI_Pack_external_size(const char datarep[], int incount, */
/*                                           MPI_Datatype datatype, MPI_Aint *size); */
/*  int MPI_Pack(const void *inbuf, int incount, MPI_Datatype datatype, */
/*                             void *outbuf, int outsize, int *position, MPI_Comm comm); */
/*  int MPI_Pack_size(int incount, MPI_Datatype datatype, MPI_Comm comm, */
/*                                  int *size); */
/*  int MPI_Pcontrol(const int level, ...); */
/*  int MPI_Probe(int source, int tag, MPI_Comm comm, MPI_Status *status); */
/*  int MPI_Publish_name(const char *service_name, MPI_Info info, */
/*                                     const char *port_name); */
/*  int MPI_Put(const void *origin_addr, int origin_count, MPI_Datatype origin_datatype, */
/*                            int target_rank, MPI_Aint target_disp, int target_count, */
/*                            MPI_Datatype target_datatype, MPI_Win win); */
/*  int MPI_Query_thread(int *provided); */
/*  int MPI_Raccumulate(const void *origin_addr, int origin_count, MPI_Datatype origin_datatype, */
/*                                    int target_rank, MPI_Aint target_disp, int target_count, */
/*                                    MPI_Datatype target_datatype, MPI_Op op, MPI_Win win, MPI_Request *request); */
/*  int MPI_Recv_init(void *buf, int count, MPI_Datatype datatype, int source, */
/*                                  int tag, MPI_Comm comm, MPI_Request *request); */
/*  int MPI_Reduce(const void *sendbuf, void *recvbuf, int count, */
/*                               MPI_Datatype datatype, MPI_Op op, int root, MPI_Comm comm); */
/*  int MPI_Ireduce(const void *sendbuf, void *recvbuf, int count, */
/*                               MPI_Datatype datatype, MPI_Op op, int root, MPI_Comm comm, MPI_Request *request); */
/*  int MPI_Reduce_local(const void *inbuf, void *inoutbuf, int count, */
/*                                     MPI_Datatype datatype, MPI_Op op); */
/*  int MPI_Reduce_scatter(const void *sendbuf, void *recvbuf, const int recvcounts[], */
/*                                       MPI_Datatype datatype, MPI_Op op, MPI_Comm comm); */
/*  int MPI_Ireduce_scatter(const void *sendbuf, void *recvbuf, const int recvcounts[], */
/*                                       MPI_Datatype datatype, MPI_Op op, MPI_Comm comm, MPI_Request *request); */
/*  int MPI_Reduce_scatter_block(const void *sendbuf, void *recvbuf, int recvcount, */
/*                                       MPI_Datatype datatype, MPI_Op op, MPI_Comm comm); */
/*  int MPI_Ireduce_scatter_block(const void *sendbuf, void *recvbuf, int recvcount, */
/*                                       MPI_Datatype datatype, MPI_Op op, MPI_Comm comm, MPI_Request *request); */
/*  int MPI_Register_datarep(const char *datarep, */
/*                                         MPI_Datarep_conversion_function *read_conversion_fn, */
/*                                         MPI_Datarep_conversion_function *write_conversion_fn, */
/*                                         MPI_Datarep_extent_function *dtype_file_extent_fn, */
/*                                         void *extra_state); */
/*  int MPI_Request_free(MPI_Request *request); */
/*  int MPI_Request_get_status(MPI_Request request, int *flag, */
/*                                           MPI_Status *status); */
/*  int MPI_Rget(void *origin_addr, int origin_count, MPI_Datatype origin_datatype, */
/*                             int target_rank, MPI_Aint target_disp, int target_count, MPI_Datatype target_datatype, */
/*                             MPI_Win win, MPI_Request *request); */
/*  int MPI_Rget_accumulate(const void *origin_addr, int origin_count, MPI_Datatype origin_datatype, */
/*                                        void *result_addr, int result_count, MPI_Datatype result_datatype, */
/*                                        int target_rank, MPI_Aint target_disp, int target_count, */
/*                                        MPI_Datatype target_datatype, MPI_Op op, */
/*                                        MPI_Win win, MPI_Request *request); */
/*  int MPI_Rput(const void *origin_addr, int origin_count, MPI_Datatype origin_datatype, */
/*                             int target_rank, MPI_Aint target_disp, int target_cout, */
/*                             MPI_Datatype target_datatype, MPI_Win win, MPI_Request *request); */
/*  int MPI_Rsend(const void *ibuf, int count, MPI_Datatype datatype, int dest, */
/*                              int tag, MPI_Comm comm); */
/*  int MPI_Rsend_init(const void *buf, int count, MPI_Datatype datatype, */
/*                                   int dest, int tag, MPI_Comm comm, */
/*                                   MPI_Request *request); */
/*  int MPI_Scan(const void *sendbuf, void *recvbuf, int count, */
/*                             MPI_Datatype datatype, MPI_Op op, MPI_Comm comm); */
/*  int MPI_Iscan(const void *sendbuf, void *recvbuf, int count, */
/*                             MPI_Datatype datatype, MPI_Op op, MPI_Comm comm, MPI_Request *request); */
/*  int MPI_Scatter(const void *sendbuf, int sendcount, MPI_Datatype sendtype, */
/*                                void *recvbuf, int recvcount, MPI_Datatype recvtype, */
/*                                int root, MPI_Comm comm); */
/*  int MPI_Iscatter(const void *sendbuf, int sendcount, MPI_Datatype sendtype, */
/*                                void *recvbuf, int recvcount, MPI_Datatype recvtype, */
/*                                int root, MPI_Comm comm, MPI_Request *request); */
/*  int MPI_Scatterv(const void *sendbuf, const int sendcounts[], const int displs[], */
/*                                 MPI_Datatype sendtype, void *recvbuf, int recvcount, */
/*                                 MPI_Datatype recvtype, int root, MPI_Comm comm); */
/*  int MPI_Iscatterv(const void *sendbuf, const int sendcounts[], const int displs[], */
/*                                 MPI_Datatype sendtype, void *recvbuf, int recvcount, */
/*                                 MPI_Datatype recvtype, int root, MPI_Comm comm, MPI_Request *request); */
/*  int MPI_Send_init(const void *buf, int count, MPI_Datatype datatype, */
/*                                  int dest, int tag, MPI_Comm comm, */
/*                                  MPI_Request *request); */
/* int MPI_Send(const void *buf, int count, MPI_Datatype datatype, int dest, */
/*                            int tag, MPI_Comm comm); */
/*  int MPI_Sendrecv(const void *sendbuf, int sendcount, MPI_Datatype sendtype, */
/*                                 int dest, int sendtag, void *recvbuf, int recvcount, */
/*                                 MPI_Datatype recvtype, int source, int recvtag, */
/*                                 MPI_Comm comm,  MPI_Status *status); */
/*  int MPI_Sendrecv_replace(void * buf, int count, MPI_Datatype datatype, */
/*                                         int dest, int sendtag, int source, int recvtag, */
/*                                         MPI_Comm comm, MPI_Status *status); */
/*  int MPI_Ssend_init(const void *buf, int count, MPI_Datatype datatype, */
/*                                   int dest, int tag, MPI_Comm comm, */
/*                                   MPI_Request *request); */
/*  int MPI_Start(MPI_Request *request); */
/*  int MPI_Startall(int count, MPI_Request array_of_requests[]); */
/*  int MPI_Status_set_cancelled(MPI_Status *status, int flag); */
/*  int MPI_Status_set_elements(MPI_Status *status, MPI_Datatype datatype, */
/*                                            int count); */
/*  int MPI_Status_set_elements_x(MPI_Status *status, MPI_Datatype datatype, */
/*                                              MPI_Count count); */
/*  int MPI_Testall(int count, MPI_Request array_of_requests[], int *flag, */
/*                                MPI_Status array_of_statuses[]); */
/*  int MPI_Testany(int count, MPI_Request array_of_requests[], int *index, */
/*                                int *flag, MPI_Status *status); */
/*  int MPI_Test(MPI_Request *request, int *flag, MPI_Status *status); */
/*  int MPI_Test_cancelled(const MPI_Status *status, int *flag); */
/*  int MPI_Testsome(int incount, MPI_Request array_of_requests[], */
/*                                 int *outcount, int array_of_indices[], */
/*                                 MPI_Status array_of_statuses[]); */
/*  int MPI_Topo_test(MPI_Comm comm, int *status); */
/*  int MPI_Type_commit(MPI_Datatype *type); */
/*  int MPI_Type_contiguous(int count, MPI_Datatype oldtype, */
/*                                        MPI_Datatype *newtype); */
/*  int MPI_Type_create_darray(int size, int rank, int ndims, */
/*                                           const int gsize_array[], const int distrib_array[], */
/*                                           const int darg_array[], const int psize_array[], */
/*                                           int order, MPI_Datatype oldtype, */
/*                                           MPI_Datatype *newtype); */
/*  int MPI_Type_create_f90_complex(int p, int r, MPI_Datatype *newtype); */
/*  int MPI_Type_create_f90_integer(int r, MPI_Datatype *newtype); */
/*  int MPI_Type_create_f90_real(int p, int r, MPI_Datatype *newtype); */
/*  int MPI_Type_create_hindexed_block(int count, int blocklength, */
/*                                                   const MPI_Aint array_of_displacements[], */
/*                                                   MPI_Datatype oldtype, */
/*                                                   MPI_Datatype *newtype); */
/*  int MPI_Type_create_hindexed(int count, const int array_of_blocklengths[], */
/*                                             const MPI_Aint array_of_displacements[], */
/*                                             MPI_Datatype oldtype, */
/*                                             MPI_Datatype *newtype); */
/*  int MPI_Type_create_hvector(int count, int blocklength, MPI_Aint stride, */
/*                                            MPI_Datatype oldtype, */
/*                                            MPI_Datatype *newtype); */
/*  int MPI_Type_create_keyval(MPI_Type_copy_attr_function *type_copy_attr_fn, */
/*                                           MPI_Type_delete_attr_function *type_delete_attr_fn, */
/*                                           int *type_keyval, void *extra_state); */
/*  int MPI_Type_create_indexed_block(int count, int blocklength, */
/*                                                  const int array_of_displacements[], */
/*                                                  MPI_Datatype oldtype, */
/*                                                  MPI_Datatype *newtype); */
/*  int MPI_Type_create_struct(int count, const int array_of_block_lengths[], */
/*                                           const MPI_Aint array_of_displacements[], */
/*                                           const MPI_Datatype array_of_types[], */
/*                                           MPI_Datatype *newtype); */
/*  int MPI_Type_create_subarray(int ndims, const int size_array[], const int subsize_array[], */
/*                                             const int start_array[], int order, */
/*                                             MPI_Datatype oldtype, MPI_Datatype *newtype); */
/*  int MPI_Type_create_resized(MPI_Datatype oldtype, MPI_Aint lb, */
/*                                            MPI_Aint extent, MPI_Datatype *newtype); */
/*  int MPI_Type_delete_attr(MPI_Datatype type, int type_keyval); */
/*  int MPI_Type_dup(MPI_Datatype type, MPI_Datatype *newtype); */
/*  int MPI_Type_free(MPI_Datatype *type); */
/*  int MPI_Type_free_keyval(int *type_keyval); */
/*  int MPI_Type_get_attr(MPI_Datatype type, int type_keyval, */
/*                                      void *attribute_val, int *flag); */
/*  int MPI_Type_get_contents(MPI_Datatype mtype, int max_integers, */
/*                                          int max_addresses, int max_datatypes, */
/*                                          int array_of_integers[], */
/*                                          MPI_Aint array_of_addresses[], */
/*                                          MPI_Datatype array_of_datatypes[]); */
/*  int MPI_Type_get_envelope(MPI_Datatype type, int *num_integers, */
/*                                          int *num_addresses, int *num_datatypes, */
/*                                          int *combiner); */
/*  int MPI_Type_get_extent(MPI_Datatype type, MPI_Aint *lb, */
/*                                        MPI_Aint *extent); */
/*  int MPI_Type_get_extent_x(MPI_Datatype type, MPI_Count *lb, */
/*                                          MPI_Count *extent); */
/*  int MPI_Type_get_name(MPI_Datatype type, char *type_name, */
/*                                      int *resultlen); */
/*  int MPI_Type_get_true_extent(MPI_Datatype datatype, MPI_Aint *true_lb, */
/*                                             MPI_Aint *true_extent); */
/*  int MPI_Type_get_true_extent_x(MPI_Datatype datatype, MPI_Count *true_lb, */
/*                                               MPI_Count *true_extent); */
/*  int MPI_Type_indexed(int count, const int array_of_blocklengths[], */
/*                                     const int array_of_displacements[], */
/*                                     MPI_Datatype oldtype, MPI_Datatype *newtype); */
/*  int MPI_Type_match_size(int typeclass, int size, MPI_Datatype *type); */
/*  int MPI_Type_set_attr(MPI_Datatype type, int type_keyval, */
/*                                      void *attr_val); */
/*  int MPI_Type_set_name(MPI_Datatype type, const char *type_name); */
/*  int MPI_Type_size(MPI_Datatype type, int *size); */
/*  int MPI_Type_size_x(MPI_Datatype type, MPI_Count *size); */
/*  int MPI_Type_vector(int count, int blocklength, int stride, */
/*                                    MPI_Datatype oldtype, MPI_Datatype *newtype); */
/*  int MPI_Unpack(const void *inbuf, int insize, int *position, */
/*                               void *outbuf, int outcount, MPI_Datatype datatype, */
/*                               MPI_Comm comm); */
/*  int MPI_Unpublish_name(const char *service_name, MPI_Info info, const char *port_name); */
/*  int MPI_Unpack_external (const char datarep[], const void *inbuf, MPI_Aint insize, */
/*                                         MPI_Aint *position, void *outbuf, int outcount, */
/*                                         MPI_Datatype datatype); */
/*  int MPI_Waitall(int count, MPI_Request array_of_requests[], */
/*                                MPI_Status *array_of_statuses); */
/*  int MPI_Waitany(int count, MPI_Request array_of_requests[], */
/*                                int *index, MPI_Status *status); */
/*  int MPI_Wait(MPI_Request *request, MPI_Status *status); */
/*  int MPI_Waitsome(int incount, MPI_Request array_of_requests[], */
/*                                 int *outcount, int array_of_indices[], */
/*                                 MPI_Status array_of_statuses[]); */
/*  int MPI_Win_allocate(MPI_Aint size, int disp_unit, MPI_Info info, */
/*                                     MPI_Comm comm, void *baseptr, MPI_Win *win); */
/*  int MPI_Win_allocate_shared(MPI_Aint size, int disp_unit, MPI_Info info, */
/*                                            MPI_Comm comm, void *baseptr, MPI_Win *win); */
/*  int MPI_Win_attach(MPI_Win win, void *base, MPI_Aint size); */
/*  int MPI_Win_call_errhandler(MPI_Win win, int errorcode); */
/*  int MPI_Win_complete(MPI_Win win); */
/*  int MPI_Win_create(void *base, MPI_Aint size, int disp_unit, */
/*                                   MPI_Info info, MPI_Comm comm, MPI_Win *win); */
/*  int MPI_Win_create_dynamic(MPI_Info info, MPI_Comm comm, MPI_Win *win); */
/*  int MPI_Win_create_errhandler(MPI_Win_errhandler_function *function, */
/*                                              MPI_Errhandler *errhandler); */
/*  int MPI_Win_create_keyval(MPI_Win_copy_attr_function *win_copy_attr_fn, */
/*                                          MPI_Win_delete_attr_function *win_delete_attr_fn, */
/*                                          int *win_keyval, void *extra_state); */
/*  int MPI_Win_delete_attr(MPI_Win win, int win_keyval); */
/*  int MPI_Win_detach(MPI_Win win, const void *base); */
/*  int MPI_Win_fence(int assert, MPI_Win win); */
/*  int MPI_Win_flush(int rank, MPI_Win win); */
/*  int MPI_Win_flush_all(MPI_Win win); */
/*  int MPI_Win_flush_local(int rank, MPI_Win win); */
/*  int MPI_Win_flush_local_all(MPI_Win win); */
/*  int MPI_Win_free(MPI_Win *win); */
/*  int MPI_Win_free_keyval(int *win_keyval); */
/*  int MPI_Win_get_attr(MPI_Win win, int win_keyval, */
/*                                     void *attribute_val, int *flag); */
/*  int MPI_Win_get_errhandler(MPI_Win win, MPI_Errhandler *errhandler); */
/*  int MPI_Win_get_group(MPI_Win win, MPI_Group *group); */
/*  int MPI_Win_get_info(MPI_Win win, MPI_Info *info_used); */
/*  int MPI_Win_get_name(MPI_Win win, char *win_name, int *resultlen); */
/*  int MPI_Win_lock(int lock_type, int rank, int assert, MPI_Win win); */
/*  int MPI_Win_lock_all(int assert, MPI_Win win); */
/*  int MPI_Win_post(MPI_Group group, int assert, MPI_Win win); */
/*  int MPI_Win_set_attr(MPI_Win win, int win_keyval, void *attribute_val); */
/*  int MPI_Win_set_errhandler(MPI_Win win, MPI_Errhandler errhandler); */
/*  int MPI_Win_set_info(MPI_Win win, MPI_Info info); */
/*  int MPI_Win_set_name(MPI_Win win, const char *win_name); */
/*  int MPI_Win_shared_query(MPI_Win win, int rank, MPI_Aint *size, int *disp_unit, void *baseptr); */
/*  int MPI_Win_start(MPI_Group group, int assert, MPI_Win win); */
/*  int MPI_Win_sync(MPI_Win win); */
/*  int MPI_Win_test(MPI_Win win, int *flag); */
/*  int MPI_Win_unlock(int rank, MPI_Win win); */
/*  int MPI_Win_unlock_all(MPI_Win win); */
/*  int MPI_Win_wait(MPI_Win win); */
/*  double MPI_Wtick(void); */
/*  double MPI_Wtime(void); */

#endif /* __FC_MPI */
