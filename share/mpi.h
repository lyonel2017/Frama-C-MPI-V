/**************************************************************************/
/*  This file is part of MPI-V plug-in of Frama-C.                        */
/*                                                                        */
/*  Copyright (C) 2020 Lionel Blatter                                     */
/*                                                                        */
/*  Lionel Blatter <lionel.blatter@kit.edu>                               */
/*                                                                        */
/*  you can redistribute it and/or modify it under the terms of the GNU   */
/*  Lesser General Public License as published by the Free Software       */
/*  Foundation, version 2.1.                                              */
/*                                                                        */
/*  It is distributed in the hope that it will be useful,                 */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         */
/*  GNU Lesser General Public License for more details.                   */
/*                                                                        */
/*  See the GNU Lesser General Public License version 2.1                 */
/*  for more details (enclosed in the file LICENSE).                      */
/**************************************************************************/

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
 * MPI Protocol
 */

/*@ axiomatic MPI_driver{
  @ type mpi_datatype;
  @
  @ logic mpi_datatype get_mpi_char;
  @ logic mpi_datatype get_mpi_int;
  @
  @ logic integer MPI_COMM_WORLD_size_ACSL;
  @ logic integer MPI_COMM_WORLD_rank_ACSL;
  @
  @ predicate size_constrain(integer size);
  @
  @ type logic_protocol;
  @
  @ logic logic_protocol seq (logic_protocol p1, logic_protocol p2);
  @
  @ logic logic_protocol the_protocol;
  @
  @ predicate isMessage(logic_protocol p);
  @ predicate isForeach(logic_protocol p);
  @ predicate isSkip(logic_protocol p);
  @ predicate isBroadcast(logic_protocol p);
  @ predicate isGather(logic_protocol p);
  @ predicate isScatter(logic_protocol p);
  @
  @ predicate isMessageforSend(logic_protocol p, integer dest, integer count, integer tag, mpi_datatype datatype);
  @ predicate isMessageforRecv(logic_protocol p, integer source, integer count, integer tag, mpi_datatype datatype);
  @ predicate isforBroadcast(logic_protocol p, integer root, integer count, mpi_datatype datatype);
  @ predicate isforGather(logic_protocol p, integer root, integer count, mpi_datatype datatype);
  @ predicate isforScatter(logic_protocol p, integer root, integer count, mpi_datatype datatype);
  @
  @ logic logic_protocol simpl(logic_protocol p);
  @ logic logic_protocol split(logic_protocol p,integer i);
  @ logic logic_protocol assoc(logic_protocol p);
  @ logic logic_protocol getFirst(logic_protocol p);
  @ logic logic_protocol getNext(logic_protocol p);
}*/

/*@ axiomatic MPI_datatype {
  @ logic mpi_datatype c_to_why_mpi_datatype (MPI_Datatype datatype);
  @ axiom mpi_int : c_to_why_mpi_datatype(MPI_INT) == get_mpi_int;
  @ axiom mpi_char : c_to_why_mpi_datatype(MPI_CHAR) == get_mpi_char;
}*/

//@ ghost struct c_protocol;

/*@ axiomatic Protocol_getter_setter{
  @ predicate set_type(struct c_protocol s, logic_protocol p);
  @ logic logic_protocol get_type(struct c_protocol s);
  @ axiom link: \forall logic_protocol p, struct c_protocol s; set_type(s,p) ==> p == get_type(s);
}*/

//@ ghost int priority = 0;

//@ ghost extern struct c_protocol protocol;

/*@ ghost
     /@ assigns protocol;
      @ ensures set_type(protocol,simpl(\old(get_type(protocol)))); @/
     void simpl();
 @*/

/*@ ghost
     /@ assigns protocol;
      @ ensures set_type(protocol,assoc(\old(get_type(protocol))));@/
     void assoc();
 @*/

/*@ ghost
     /@ assigns protocol;
      @ ensures \let p = \old(get_type(protocol));
                set_type(protocol,seq(simpl(getFirst(p)),getNext(p)));@/
      void unroll();
  @*/

/*@ ghost
     /@ requires isSkip(simpl(getFirst(get_type(protocol))));
      @ assigns protocol;
      @ ensures set_type(protocol,getNext(\old(get_type(protocol))));@/
     void toskip();
  @*/

/*
 * MPI Mem
 */

/*
 *l1: require support for handling communicator that are created: require support of dynamique alloction
 *l2: require support for MPI general datatype
*/

/*
 * MPI API
 */

/*@ requires not_mpi_section: priority == 0;
  @ requires size_constrain(MPI_COMM_WORLD_size_ACSL) ==> MPI_COMM_WORLD_size_ACSL > 0;
  @ ensures 0 <= MPI_COMM_WORLD_rank_ACSL < MPI_COMM_WORLD_size_ACSL;
  @ ensures size_constrain(MPI_COMM_WORLD_size_ACSL);
  @ ensures set_protocol: set_type(protocol,the_protocol);
  @ ensures open_mpi_section: priority == 1;
  @ assigns \result, protocol, priority;*/
int MPI_Init(int *argc, char ***argv);

/*@ requires in_mpi_section: priority == 1;
  @ requires \valid(rank);
  @ requires comm == MPI_COMM_WORLD; // limitation l1
  @ ensures MPI_COMM_WORLD_rank_ACSL == *rank;
  @ assigns *rank, \result;*/
int MPI_Comm_rank(MPI_Comm comm, int *rank);

/*@ requires in_mpi_section: priority == 1;
  @ requires \valid(size);
  @ requires comm == MPI_COMM_WORLD; // limitation l1
  @ ensures MPI_COMM_WORLD_size_ACSL == *size;
  @ assigns *size, \result;*/
int MPI_Comm_size(MPI_Comm comm, int *size);

/*@ requires protocol_is_empty: isSkip(get_type(protocol));
  @ requires in_mpi_section: priority == 1;
  @ assigns \result, protocol, priority;
  @ ensures close_mpi_section: priority == 2;*/
int MPI_Finalize(void);

/*@ requires in_mpi_section: priority == 1;
  @ requires is_comm_worl: comm == MPI_COMM_WORLD; // limitation l1
  @ requires destination_in_world: 0 <= dest < MPI_COMM_WORLD_size_ACSL;
  @ requires destination_is_not_me: dest != MPI_COMM_WORLD_rank_ACSL;
  @ requires count_is_not_neg: 0 <= count;
  @ requires tag_is_no_neg: 0 <= tag;
  @ requires datatype: datatype == MPI_CHAR; // instantiate check if the type is supported
  @ requires protocol_for_ssend: isMessageforSend(getFirst(get_type(protocol)),dest,count,tag,c_to_why_mpi_datatype(datatype));
  @ requires initialization_buf: \initialized((char *)buf + (0 .. count - 1));
  @ requires danglingness_buf: \forall integer i; 0 ≤ i < count ⇒ ¬\dangling((char*)buf + i);
  @ requires valid_buf: ((\block_length((char*)buf) == 0 && \offset((char*)buf) == 0) && count == 0) || \valid_read(((char*)buf)+(0..count-1));
  @ ensures reduce_protocol: set_type(protocol,getNext(\old(get_type(protocol))));
  @ assigns \result,protocol;
*/
int MPI_Ssend(const void *buf, int count, MPI_Datatype datatype, int dest, int tag, MPI_Comm comm);

/* the nonblock communication will spone in the protocol the requirement
   to check termination of the communication.
   Cannot be done, because WP does not support dynamic allocation for the request
 */
/*  int MPI_Issend(const void *buf, int count, MPI_Datatype datatype, int dest, */
/*                               int tag, MPI_Comm comm, MPI_Request *request); */

/*@ requires in_mpi_section: priority == 1;
  @ requires is_comm_world: comm == MPI_COMM_WORLD; // limitation l1
  @ requires source_in_world: 0 <= source < MPI_COMM_WORLD_size_ACSL; //|| source == MPI_ANY_SOURCE;
  @ requires source_is_not_me: source != MPI_COMM_WORLD_rank_ACSL;
  @ requires tag_is_not_neg: 0 <= tag; //|| tag == MPI_ANY_TAG;
  @ requires count_is_not_neg: 0 <= count;
  @ requires datatype: datatype == MPI_CHAR; //limitation l2
  @ requires status == MPI_STATUS_IGNORE;
  @ requires protocol_for_recv: isMessageforRecv(getFirst(get_type(protocol)),source,count,tag,c_to_why_mpi_datatype(datatype));
  @ requires initialization_buf: \initialized((char *)buf + (0 .. count - 1));
  @ requires danglingness_buf: \forall integer i; 0 ≤ i < count ⇒ ¬\dangling((char*)buf + i);
  @ requires valid_buf: ((\block_length((char*)buf) == 0 && \offset((char*)buf) == 0) && count == 0) || \valid(((char*)buf)+(0..count-1));
  @ ensures reduce_protocol: set_type(protocol,getNext(\old(get_type(protocol))));
  @ assigns \result,protocol;
  @ assigns assigns_buf: ((char *)buf)[0..count-1];
*/
int MPI_Recv(void* buf, int count, MPI_Datatype datatype,
	     int source, int tag, MPI_Comm comm, MPI_Status* status);

/*like a recv but does not consume the protocol message*/
/*  int MPI_Probe(int source, int tag, MPI_Comm comm, MPI_Status *status); */

/*@ requires in_mpi_section: priority == 1;
  @ requires is_comm_world: comm == MPI_COMM_WORLD; // limitation l1
  @ requires count_is_not_neg: 0 <= count;
  @ requires root_in_world: 0 <= root < MPI_COMM_WORLD_size_ACSL;
  @ requires datatype: datatype == MPI_CHAR;
  @ requires protocol_for_bcast: isforBroadcast(getFirst(get_type(protocol)),root,count,c_to_why_mpi_datatype(datatype));
  @ ensures reduce_protocol: set_type(protocol,getNext(\old(get_type(protocol))));
  @ assigns \result,protocol;
  @ behavior type_root :
  @   assumes MPI_COMM_WORLD_rank_ACSL == root;
  @   requires valid_buf: ((\block_length((char*)buf) == 0 && \offset((char*)buf) == 0) && count == 0) ||
                          \valid(((char*)buf)+(0..count-1));
  @   requires initialization_buf: \initialized((char *)buf + (0 .. count - 1));
  @   requires danglingness_buf: \forall integer i; 0 ≤ i < count ⇒ ¬\dangling((char*)buf + i);
  @   assigns ((char *)buf)[0..count-1];
  @ behavior type_not_root :
  @   assumes MPI_COMM_WORLD_rank_ACSL != root;
  @   requires valid_buf: ((\block_length((char*)buf) == 0 && \offset((char*)buf) == 0) && count == 0) ||
                           \valid_read(((char*)buf)+(0..count-1));
  @   requires danglingness_buf: \forall integer i; 0 ≤ i < count ⇒ ¬\dangling((char*)buf + i);
  @   assigns ((char *)buf)[0..count-1];
*/
int MPI_Bcast(void *buf, int count, MPI_Datatype datatype,
                             int root, MPI_Comm comm);

/*@ requires in_mpi_section: priority == 1;
  @ requires is_comm_world: comm == MPI_COMM_WORLD; //limitation l1
  @ requires sendcount_is_not_neg: 0 <= sendcount;
  @ requires datatype: sendtype == MPI_CHAR;
  @ requires recvcount_is_not_neg: 0 <= recvcount;
  @ requires datatype: recvtype == MPI_CHAR;
  @ requires root_in_worlf: 0 <= root < MPI_COMM_WORLD_size_ACSL;
  @ requires recvtype == sendtype && recvcount == sendcount; //limitation l2
  @ requires protocol_for_gather: isforGather(getFirst(get_type(protocol)),root,sendcount,c_to_why_mpi_datatype(sendtype));
  @ ensures reduce_protocol: set_type(protocol,getNext(\old(get_type(protocol))));
  @ assigns \result,protocol;
  @ behavior type_root :
  @   assumes MPI_COMM_WORLD_rank_ACSL == root;
  @   requires valid_buf: ((\block_length((char*)sendbuf) == 0 && \offset((char*)sendbuf) == 0) && sendcount == 0) ||
                          \valid_read(((char*)sendbuf)+(0..sendcount-1));
  @   requires initialization_buf: \initialized((char *)sendbuf + (0 .. sendcount - 1));
  @   requires danglingness_buf: \forall integer i; 0 ≤ i < sendcount ⇒ ¬\dangling((char*)sendbuf + i);
  @   requires valid_buf: ((\block_length((char*)recvbuf) == 0 && \offset((char*)recvbuf) == 0) && recvcount == 0) ||
                          \valid(((char*)recvbuf)+(0..recvcount*MPI_COMM_WORLD_size_ACSL-1));
  @   requires danglingness_buf: \forall integer i; 0 ≤ i < recvcount*MPI_COMM_WORLD_size_ACSL ⇒ ¬\dangling((char*)recvbuf + i);
  @   assigns ((char *)recvbuf)[0..recvcount*MPI_COMM_WORLD_size_ACSL-1];
  @ behavior type_not_root :
  @   assumes MPI_COMM_WORLD_rank_ACSL != root;
  @   requires valid_buf: ((\block_length((char*)sendbuf) == 0 && \offset((char*)sendbuf) == 0) && sendcount == 0) ||
                          \valid_read(((char*)sendbuf)+(0..sendcount-1));
  @   requires initialization_buf: \initialized((char *)sendbuf + (0 .. sendcount - 1));
  @   requires danglingness_buf: \forall integer i; 0 ≤ i < sendcount ⇒ ¬\dangling((char*)sendbuf + i);
*/
int MPI_Gather(const void *sendbuf, int sendcount, MPI_Datatype sendtype,
	       void *recvbuf, int recvcount, MPI_Datatype recvtype,
	       int root, MPI_Comm comm);

/*@ requires in_mpi_section: priority == 1;
  @ requires is_comm_world: comm == MPI_COMM_WORLD; //limitation l1
  @ requires sendcount_not_neg : 0 <= sendcount;
  @ requires datatype: sendtype == MPI_CHAR;
  @ requires recvcount_not_neg: 0 <= recvcount;
  @ requires datatype: recvtype == MPI_CHAR;
  @ requires root_in_worlf: 0 <= root < MPI_COMM_WORLD_size_ACSL;
  @ requires recvtype == sendtype && recvcount == sendcount; //limitation l2
  @ requires protoocl_for_scatter: isforScatter(getFirst(get_type(protocol)),root,sendcount,c_to_why_mpi_datatype(sendtype));
  @ ensures reduce_protocol: set_type(protocol,getNext(\old(get_type(protocol))));
  @ assigns \result,protocol;
  @ behavior type_root :
  @   assumes MPI_COMM_WORLD_rank_ACSL == root;
  @   requires valid_buf: ((\block_length((char*)recvbuf) == 0 && \offset((char*)recvbuf) == 0) && recvcount == 0) ||
                          \valid(((char*)recvbuf)+(0..recvcount-1));
  @   requires danglingness_buf: \forall integer i; 0 ≤ i < recvcount ⇒ ¬\dangling((char*)recvbuf + i);
  @   requires valid_buf: ((\block_length((char*)sendbuf) == 0 && \offset((char*)sendbuf) == 0) && sendcount == 0) ||
                          \valid_read(((char*)sendbuf)+(0..sendcount*MPI_COMM_WORLD_size_ACSL-1));
  @   requires initialization_buf: \initialized((char *)sendbuf + (0 .. sendcount*MPI_COMM_WORLD_size_ACSL - 1));
  @   requires danglingness_buf: \forall integer i; 0 ≤ i < sendcount*MPI_COMM_WORLD_size_ACSL ⇒ ¬\dangling((char*)sendbuf + i);
  @   assigns ((char *)recvbuf)[0..recvcount-1];
 @ behavior type_not_root :
  @   assumes MPI_COMM_WORLD_rank_ACSL != root;
  @   requires valid_buf: ((\block_length((char*)recvbuf) == 0 && \offset((char*)recvbuf) == 0) && recvcount == 0) ||
                          \valid(((char*)recvbuf)+(0..recvcount-1));
  @   requires danglingness_buf: \forall integer i; 0 ≤ i < recvcount ⇒ ¬\dangling((char*)recvbuf + i);
  @   assigns ((char *)recvbuf)[0..recvcount-1];
*/
int MPI_Scatter(const void *sendbuf, int sendcount, MPI_Datatype sendtype,
		void *recvbuf, int recvcount, MPI_Datatype recvtype,
		int root, MPI_Comm comm);

int MPI_Reduce(const void *sendbuf, void *recvbuf, int count,
                              MPI_Datatype datatype, MPI_Op op, int root, MPI_Comm comm);

#endif /* __FC_MPI */
