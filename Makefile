##########################################################################
#  This file is part of MPI-V plug-in of Frama-C.                        #
#                                                                        #
#  Copyright (C) 2020 Lionel Blatter                                     #
#                                                                        #
#  Lionel Blatter <lionel.blatter@kit.edu>                               #
#                                                                        #
#  you can redistribute it and/or modify it under the terms of the GNU   #
#  Lesser General Public License as published by the Free Software       #
#  Foundation, version 2.1.                                              #
#                                                                        #
#  It is distributed in the hope that it will be useful,                 #
#  but WITHOUT ANY WARRANTY; without even the implied warranty of        #
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         #
#  GNU Lesser General Public License for more details.                   #
#                                                                        #
#  See the GNU Lesser General Public License version 2.1                 #
#  for more details (enclosed in the file LICENSE).                      #
##########################################################################

ifndef FRAMAC_SHARE
FRAMAC_SHARE  :=$(shell frama-c-config -print-share-path)
endif
ifndef FRAMAC_LIBDIR
FRAMAC_LIBDIR :=$(shell frama-c-config -print-libpath)
endif

PLUGIN_ENABLE:=yes
PLUGIN_DYNAMIC:=yes
PLUGIN_DISTRIBUTED:=$(PLUGIN_ENABLE)
PLUGIN_DEPENDENCIES:= WP

PLUGIN_NAME := MPI_V

PLUGIN_CMO := MPI_V_options \
	MPI_V_core \
	mpi_utils \
	mpi_recv \
	mpi_ssend \
	mpi_broadcast \
	mpi_gather \
	mpi_allgather \
	mpi_scatter \
	mpi_reduce \
	mpi_allreduce \
	mpi_main \
	MPI_V_register
PLUGIN_TESTS_DIRS := test

include $(FRAMAC_SHARE)/Makefile.dynamic

install::
	$(PRINT_INSTALL) MPI-V share files
	$(MKDIR) $(FRAMAC_DATADIR)/mpi-v
	$(CP) $(MPI_V_DIR)/share/mpi.h $(FRAMAC_DATADIR)/mpi-v
	$(CP) $(MPI_V_DIR)/share/protocol.why $(FRAMAC_DATADIR)/mpi-v
	$(CP) $(MPI_V_DIR)/share/mpi.driver $(FRAMAC_DATADIR)/mpi-v

uninstall::
	$(PRINT_RM) MPI-V share files
	$(RM) -r $(FRAMAC_DATADIR)/mpi-v

MPI_V_DISTRIBUTED_FILES=MPI_V_options.ml MPI_V_options.mli \
	MPI_V_core.ml MPI_V_core.mli \
	mpi_utils.ml mpi_utils.mli \
	mpi_recv.ml mpi_recv.mli \
	mpi_ssend.ml mpi_ssend.mli  \
	mpi_broadcast.ml mpi_broadcast.mli \
	mpi_gather.ml mpi_gather.mli \
	mpi_allgather.ml mpi_allgather.mli \
	mpi_scatter.ml mpi_scatter.mli \
	mpi_reduce.ml mpi_reduce.mli \
	mpi_allreduce.ml mpi_allreduce.mli \
	mpi_main.ml mpi_main.mli \
	MPI_V_register.ml MPI_V_register.mli\
	Makefile \
	MPI_V.mli \
	share/mpi.h \
	share/mpi.driver \
	share/protocol.why

headers::
	$(PRINT_MAKING) $@
	headache -c .headache_config.txt \
                 -h .LICENSE \
                 $(MPI_V_DISTRIBUTED_FILES)
