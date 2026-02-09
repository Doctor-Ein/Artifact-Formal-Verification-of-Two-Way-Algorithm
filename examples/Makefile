CURRENT_DIR=.
SETS_DIR      = ../sets
FIXPOINT_DIR  = ../fixedpoints
MONADLIB_DIR  = ../monadlib
LISTLIB_DIR   = ../ListLibDev

COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

FLAG = -R $(SETS_DIR) SetsClass \
			 -R $(FIXPOINT_DIR) FP \
			 -R $(MONADLIB_DIR) MonadLib \
			 -Q $(LISTLIB_DIR) ListLib \
			 -R . Examples

FILES = ListLib_Extend.v ListLib_Period.v ListLib_Cmp.v Preprocessing.v TwoWayMatch.v

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $(<F)
	@$(COQC) $(FLAG) $<

all: \
  $(FILES:%.v=%.vo)

_CoqProject:
	@echo $(FLAG) > _CoqProject

depend: $(FILES)
	$(COQDEP) $(FLAG) $(FILES) > .depend

.depend: $(FILES)
	@$(COQDEP) $(FLAG) $(FILES) > .depend

clean:
	@rm *.vo *.glob *.vos *.vok .*.aux

.DEFAULT_GOAL := all

-include .depend
