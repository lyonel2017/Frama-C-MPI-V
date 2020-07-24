ifndef FRAMAC_SHARE
FRAMAC_SHARE  :=$(shell frama-c-config -print-share-path)
endif
ifndef FRAMAC_LIBDIR
FRAMAC_LIBDIR :=$(shell frama-c-config -print-libpath)
endif

PLUGIN_ENABLE:=yes
PLUGIN_DYNAMIC:=yes
PLUGIN_DISTRIBUTED:=$(PLUGIN_ENABLE)

PLUGIN_NAME := MPI_V

PLUGIN_CMO := MPI_V_options \
	mpi_utils \
	mpi_recv \
	mpi_ssend \
	MPI_V_register
PLUGIN_TESTS_DIRS := test

include $(FRAMAC_SHARE)/Makefile.dynamic

install::
	$(PRINT_INSTALL) MPI-V share files
	$(MKDIR) $(FRAMAC_DATADIR)/mpi-v
	$(CP) $(MPI_V_DIR)/share/mpi.h $(FRAMAC_DATADIR)/mpi-v

uninstall::
	$(PRINT_RM) MPI-V share files
	$(RM) -r $(FRAMAC_DATADIR)/mpi-v


headers::
	$(PRINT_MAKING) $@
	headache -c .headache_config.txt \
                 -h .LICENSE \
                 $(RPP_DISTRIBUTED_FILES)
