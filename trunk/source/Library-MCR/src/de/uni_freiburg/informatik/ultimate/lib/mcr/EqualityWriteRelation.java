package de.uni_freiburg.informatik.ultimate.lib.mcr;

import java.util.List;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.lib.mcr.Mcr.IWriteRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

public class EqualityWriteRelation<LETTER extends IIcfgTransition<?>> implements IWriteRelation<LETTER> {
	@Override
	public boolean areRelated(final LETTER write1, final LETTER write2, final IProgramVar var,
			final List<LETTER> trace, final List<IPredicate> interpolants) {
		return Objects.equals(write1, write2);
	}
}
