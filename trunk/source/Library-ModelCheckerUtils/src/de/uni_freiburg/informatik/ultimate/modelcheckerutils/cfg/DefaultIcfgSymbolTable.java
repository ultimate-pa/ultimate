/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */package de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Default implementation of an {@link IIcfgSymbolTable}
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class DefaultIcfgSymbolTable implements IIcfgSymbolTable {

	protected final Map<TermVariable, IProgramVar> mTermVariable2ProgramVar = new HashMap<>();
	protected final Map<ApplicationTerm, IProgramConst> mAppTerm2ProgramConst = new HashMap<>();

	protected final Set<IProgramNonOldVar> mGlobals = new HashSet<>();
	protected final Set<IProgramConst> mConstants = new HashSet<>();
	protected final HashRelation<String, ILocalProgramVar> mLocals = new HashRelation<>();

	protected boolean mConstructionFinished = false;

	/**
	 * Constructor for empty symbol table.
	 */
	public DefaultIcfgSymbolTable() {
	}

	/**
	 * Constructs copy of {@link IIcfgSymbolTable}
	 */
	public DefaultIcfgSymbolTable(final IIcfgSymbolTable symbolTable, final Set<String> procs) {
		for (final IProgramConst constant : symbolTable.getConstants()) {
			add(constant);
		}
		for (final IProgramNonOldVar nonold : symbolTable.getGlobals()) {
			add(nonold);
		}
		for (final String proc : procs) {
			for (final ILocalProgramVar local : symbolTable.getLocals(proc)) {
				add(local);
			}
		}
		assert checkGlobals();
	}

	@Override
	public IProgramVar getProgramVar(final TermVariable tv) {
		return mTermVariable2ProgramVar.get(tv);
	}

	@Override
	public IProgramConst getProgramConst(final ApplicationTerm smtConstant) {
		return mAppTerm2ProgramConst.get(smtConstant);
	}

	@Override
	public Set<IProgramNonOldVar> getGlobals() {
		return Collections.unmodifiableSet(mGlobals);
	}

	@Override
	public Set<IProgramConst> getConstants() {
		return Collections.unmodifiableSet(mConstants);
	}

	@Override
	public Set<ILocalProgramVar> getLocals(final String proc) {
		final Set<ILocalProgramVar> locals = mLocals.getImage(proc);
		if (locals == null) {
			return Collections.emptySet();
		}
		return Collections.unmodifiableSet(mLocals.getImage(proc));
	}

	public void add(final IProgramVarOrConst varOrConst) {
		if (mConstructionFinished) {
			throw new IllegalStateException("Construction finished, unable to add new variables or constants.");
		}

		if (varOrConst instanceof IProgramConst) {
			final IProgramConst pc = (IProgramConst) varOrConst;
			mConstants.add(pc);
			mAppTerm2ProgramConst.put(pc.getDefaultConstant(), pc);
		} else if (varOrConst instanceof IProgramVar) {
			final IProgramVar var = (IProgramVar) varOrConst;
			mTermVariable2ProgramVar.put(var.getTermVariable(), var);
			if (var instanceof IProgramOldVar || var.isOldvar()) {
				throw new IllegalArgumentException("cannot add oldvar, add nonoldvar instead: " + var);
			} else if (var instanceof ILocalProgramVar) {
				mLocals.addPair(var.getProcedure(), (ILocalProgramVar) var);
			} else if (var instanceof IProgramNonOldVar) {
				final IProgramNonOldVar nonOldVar = (IProgramNonOldVar) var;
				mGlobals.add(nonOldVar);
				final IProgramOldVar oldVar = nonOldVar.getOldVar();
				mTermVariable2ProgramVar.put(oldVar.getTermVariable(), oldVar);
				assert Objects.equals(oldVar.getNonOldVar(),
						var) : "getNonOldVar() and getOldVar() should match, but do not! Oldvar: " + oldVar + " Var: "
								+ var;
			} else {
				throw new AssertionError("unknown kind of variable");
			}
		} else {
			throw new AssertionError("unknown kind of variable");
		}
	}

	/**
	 * Make this {@link IIcfgSymbolTable} unmodifiable.
	 */
	public void finishConstruction() {
		mConstructionFinished = true;
		assert checkGlobals();
	}

	private boolean checkGlobals() {
		if (mTermVariable2ProgramVar.entrySet().stream().anyMatch(a -> a.getValue() == null)) {
			throw new AssertionError("Null entry in TermVar2ProgramVar");
		}

		final Set<IProgramVar> programVars = mTermVariable2ProgramVar.entrySet().stream()
				.map(Entry<TermVariable, IProgramVar>::getValue).collect(Collectors.toSet());
		final Set<IProgramVar> oldVars = programVars.stream().filter(IProgramVar::isOldvar).collect(Collectors.toSet());
		final Optional<IProgramOldVar> any = oldVars.stream().map(a -> (IProgramOldVar) a)
				.filter(a -> !programVars.contains(a.getNonOldVar())).findAny();
		if (any.isPresent()) {
			throw new AssertionError("old var with no corresponding var: " + any.get());
		}

		return true;
	}

	@Override
	public Set<ApplicationTerm> computeAllDefaultConstants() {
		final Set<ApplicationTerm> rtr = new LinkedHashSet<>();
		mGlobals.stream().map(a -> a.getDefaultConstant()).forEachOrdered(rtr::add);
		mLocals.entrySet().stream().map(a -> a.getValue().getDefaultConstant()).forEachOrdered(rtr::add);
		return rtr;
	}

}