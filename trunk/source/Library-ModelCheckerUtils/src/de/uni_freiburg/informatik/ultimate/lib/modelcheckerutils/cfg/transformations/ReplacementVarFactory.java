/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
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
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.ConstantFinder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Factory for constructing ReplacementVars ensures that for each defining Term exactly one ReplacementVar is
 * constructed.
 * 
 * @author Matthias Heizmann
 *
 */
public class ReplacementVarFactory {

	private final ManagedScript mMgdScript;
	private final CfgSmtToolkit mCsToolkit;
	private final Map<Term, IReplacementVarOrConst> mRepVarMapping = new HashMap<>();
	private final Map<String, TermVariable> mAuxVarMapping = new HashMap<>();
	private final boolean mUseIntraproceduralReplacementVar;

	/**
	 * @param useIntraproceduralReplacementVars
	 *            construct always only {@link IntraproceduralReplacementVar} instead of {@link LocalReplacementVar},
	 *            {@link ReplacementOldVar}, {@link ReplacementNonOldVar}, and {@link ReplacementConst}.
	 */
	public ReplacementVarFactory(final CfgSmtToolkit csToolkit, final boolean useIntraproceduralReplacementVars) {
		super();
		mMgdScript = csToolkit.getManagedScript();
		mCsToolkit = csToolkit;
		mUseIntraproceduralReplacementVar = useIntraproceduralReplacementVars;
	}

	/**
	 * Get the ReplacementVar that is used as a replacement for the Term definition. Construct this ReplacementVar if it
	 * does not exist yet.
	 * 
	 * @param useGlobalVarInsteadOfConstant
	 *            do not construct constant, construct global var (and corresponding oldvar) instead.
	 */
	public IReplacementVarOrConst getOrConstuctReplacementVar(final Term definition,
			final boolean useGlobalVarInsteadOfConstant) {
		final IReplacementVarOrConst repVar = mRepVarMapping.get(definition);
		if (repVar != null) {
			return repVar;
		}
		final String nameCandidate = "rep" + SmtUtils.removeSmtQuoteCharacters(definition.toString());
		final TermVariable tv = mMgdScript.constructFreshTermVariable(nameCandidate, definition.getSort());

		final IReplacementVarOrConst newRepVar;
		if (mUseIntraproceduralReplacementVar) {
			newRepVar = new IntraproceduralReplacementVar(tv.getName(), definition, tv);
			mRepVarMapping.put(definition, newRepVar);
		} else {
			final Pair<Set<Class<? extends IProgramVarOrConst>>, Set<String>> analysisResult =
					analyzeDefinition(definition);
			if (analysisResult.getFirst().contains(IProgramNonOldVar.class)
					&& analysisResult.getFirst().contains(IProgramOldVar.class)) {
				throw new UnsupportedOperationException("nonold and old");
			} else if (analysisResult.getFirst().contains(ILocalProgramVar.class)) {
				if (analysisResult.getSecond().size() > 1) {
					throw new UnsupportedOperationException("more than one procedure");
				}
				final String proc = analysisResult.getSecond().iterator().next();
				newRepVar = constructLocalReplacementVar(definition, tv, proc);
				mRepVarMapping.put(definition, newRepVar);
			} else if (analysisResult.getFirst().contains(IProgramNonOldVar.class)) {
				final ReplacementOldVar oldVar = constructOldNonOldPairForNonOldDefinition(definition, tv);
				final ReplacementNonOldVar nonOldVar = (ReplacementNonOldVar) oldVar.getNonOldVar();
				mRepVarMapping.put(oldVar.getDefinition(), oldVar);
				mRepVarMapping.put(nonOldVar.getDefinition(), nonOldVar);
				newRepVar = nonOldVar;
			} else if (analysisResult.getFirst().contains(IProgramOldVar.class)) {
				final ReplacementOldVar oldVar = constructOldNonOldPairForOldVarDefinition(definition, tv);
				final ReplacementNonOldVar nonOldVar = (ReplacementNonOldVar) oldVar.getNonOldVar();
				mRepVarMapping.put(oldVar.getDefinition(), oldVar);
				mRepVarMapping.put(nonOldVar.getDefinition(), nonOldVar);
				newRepVar = oldVar;
			} else {
				if (useGlobalVarInsteadOfConstant) {
					final ReplacementOldVar oldVar = constructOldNonOldPairForNonOldDefinition(definition, tv);
					final ReplacementNonOldVar nonOldVar = (ReplacementNonOldVar) oldVar.getNonOldVar();
					mRepVarMapping.put(oldVar.getDefinition(), oldVar);
					mRepVarMapping.put(nonOldVar.getDefinition(), nonOldVar);
					newRepVar = nonOldVar;
				} else {
					newRepVar = constructReplacementConst(definition, tv);
					mRepVarMapping.put(definition, newRepVar);
				}
			}
		}
		assert checkOldVar(newRepVar) : newRepVar + " breaks oldVar-nonOldVar relation";
		
		return newRepVar;

	}

	private boolean checkOldVar(final IReplacementVarOrConst newRepVar) {
		if (newRepVar instanceof IProgramOldVar) {
			final IProgramOldVar oldVar = (IProgramOldVar) newRepVar;
			return Objects.equals(oldVar, oldVar.getNonOldVar().getOldVar());
		}
		if (newRepVar instanceof IProgramNonOldVar) {
			final IProgramNonOldVar var = (IProgramNonOldVar) newRepVar;
			return Objects.equals(var, var.getOldVar().getNonOldVar());
		}
		return true;
	}

	
	/**
	 * Construct both, the oldVar and the non-oldVar for a definition that
	 * represents the oldVar
	 * @return the oldVar
	 */
	private ReplacementOldVar constructOldNonOldPairForOldVarDefinition(final Term oldVarDefinition,
			final TermVariable oldVarTv) {
		final ReplacementOldVar oldVar = constructReplacementOldVar(oldVarDefinition, oldVarTv);
		final Term definition = oldVar.getDefinition();
		final Term nonOldVarDefinition =
				ProgramVarUtils.renameOldGlobalsToNonOldGlobals(definition, mCsToolkit.getSymbolTable(), mMgdScript);
		final TermVariable nonoldVarTv =
				mMgdScript.constructFreshTermVariable("nonold(" + oldVar.getIdentifierOfNonOldVar() + ")", definition.getSort());
		constructReplacementNonOldVar(nonOldVarDefinition, nonoldVarTv, oldVar);
		return oldVar;
		
	}

	/**
	 * Construct both, the oldVar and the non-oldVar for a definition that
	 * represents the non-oldVar
	 * @return the oldVar
	 */
	private ReplacementOldVar constructOldNonOldPairForNonOldDefinition(final Term nonOldDefinition,
			final TermVariable nonOldTv) {
		final Term oldVarDefinition =
				ProgramVarUtils.renameNonOldGlobalsToOldGlobals(nonOldDefinition, mCsToolkit.getSymbolTable(), mMgdScript);
		final TermVariable oldVarTv =
				mMgdScript.constructFreshTermVariable("old(" + nonOldTv.getName() + ")", nonOldDefinition.getSort());
		final ReplacementOldVar oldVar = constructReplacementOldVar(oldVarDefinition, oldVarTv);
		constructReplacementNonOldVar(nonOldDefinition, nonOldTv, oldVar);
		return oldVar;
	}

	private ReplacementConst constructReplacementConst(final Term definition, final TermVariable tv) {
		mMgdScript.lock(this);
		mMgdScript.declareFun(this, tv.getName(), new Sort[0], tv.getSort());
		final ApplicationTerm smtConstant = (ApplicationTerm) mMgdScript.term(this, tv.getName());
		mMgdScript.unlock(this);
		return new ReplacementConst(tv.getName(), smtConstant, definition);
	}

	private LocalReplacementVar constructLocalReplacementVar(final Term definition, final TermVariable tv,
			final String proc) {
		mMgdScript.lock(this);
		final ApplicationTerm defaultConstant =
				ProgramVarUtils.constructDefaultConstant(mMgdScript, this, tv.getSort(), tv.getName());
		final ApplicationTerm primedContant =
				ProgramVarUtils.constructPrimedConstant(mMgdScript, this, tv.getSort(), tv.getName());
		mMgdScript.unlock(this);
		return new LocalReplacementVar(tv.getName(), proc, tv, defaultConstant, primedContant, definition);
	}

	private ReplacementOldVar constructReplacementOldVar(final Term definition, final TermVariable tv) {
		mMgdScript.lock(this);
		final ApplicationTerm defaultConstant =
				ProgramVarUtils.constructDefaultConstant(mMgdScript, this, tv.getSort(), tv.getName());
		final ApplicationTerm primedContant =
				ProgramVarUtils.constructPrimedConstant(mMgdScript, this, tv.getSort(), tv.getName());
		mMgdScript.unlock(this);
		return new ReplacementOldVar(tv.getName(), tv, defaultConstant, primedContant, definition);
	}

	private ReplacementNonOldVar constructReplacementNonOldVar(final Term definition, final TermVariable tv,
			final ReplacementOldVar oldVar) {
		mMgdScript.lock(this);
		final ApplicationTerm defaultConstant =
				ProgramVarUtils.constructDefaultConstant(mMgdScript, this, tv.getSort(), tv.getName());
		final ApplicationTerm primedContant =
				ProgramVarUtils.constructPrimedConstant(mMgdScript, this, tv.getSort(), tv.getName());
		mMgdScript.unlock(this);
		final ReplacementNonOldVar repNonOldVar =
				new ReplacementNonOldVar(tv.getName(), tv, defaultConstant, primedContant, oldVar, definition);
		oldVar.setNonOldVar(repNonOldVar);
		return repNonOldVar;
	}

	/**
	 * Construct and return a unique TermVariable with the given name.
	 */
	public TermVariable getOrConstructAuxVar(final String name, final Sort sort) {
		TermVariable auxVar = mAuxVarMapping.get(name);
		if (auxVar == null) {
			auxVar = mMgdScript.constructFreshTermVariable(SmtUtils.removeSmtQuoteCharacters(name), sort);
			mAuxVarMapping.put(name, auxVar);
		} else {
			if (sort != auxVar.getSort()) {
				throw new AssertionError("cannot construct auxVars with same name and different sort");
			}
		}
		return auxVar;
	}

	private Pair<Set<Class<? extends IProgramVarOrConst>>, Set<String>> analyzeDefinition(final Term definition) {
		final Set<Class<? extends IProgramVarOrConst>> constOrVarKinds = new HashSet<>();
		final Set<String> procs = new HashSet<>();

		for (final TermVariable tv : definition.getFreeVars()) {
			final IProgramVar pv = mCsToolkit.getSymbolTable().getProgramVar(tv);
			if (pv instanceof ILocalProgramVar) {
				constOrVarKinds.add(ILocalProgramVar.class);
				procs.add(pv.getProcedure());
			} else if (pv instanceof IProgramNonOldVar) {
				constOrVarKinds.add(IProgramNonOldVar.class);
			} else if (pv instanceof IProgramOldVar) {
				constOrVarKinds.add(IProgramOldVar.class);
			} else {
				throw new AssertionError("unknown kind of variable");
			}
		}
		final Set<ApplicationTerm> constants = new ConstantFinder().findConstants(definition, true);
		if (!constants.isEmpty()) {
			constOrVarKinds.add(IProgramConst.class);
		}
		return new Pair<>(constOrVarKinds, procs);
	}

	public IIcfgSymbolTable constructIIcfgSymbolTable() {
		final DefaultIcfgSymbolTable result =
				new DefaultIcfgSymbolTable(mCsToolkit.getSymbolTable(), mCsToolkit.getProcedures());
		for (final Entry<Term, IReplacementVarOrConst> entry : mRepVarMapping.entrySet()) {
			if (!(entry.getValue() instanceof IProgramOldVar)) {
				result.add(entry.getValue());
			}
		}
		result.finishConstruction();
		return result;
	}

	public ModifiableGlobalsTable constructModifiableGlobalsTable() {
		final HashRelation<String, IProgramNonOldVar> proc2Globals = new HashRelation<>();
		// construct copy
		for (final String proc : mCsToolkit.getProcedures()) {
			final Set<IProgramNonOldVar> mod = mCsToolkit.getModifiableGlobalsTable().getModifiedBoogieVars(proc);
			for (final IProgramNonOldVar nonOld : mod) {
				proc2Globals.addPair(proc, nonOld);
			}
		}
		// add new vars
		// this is just a workaround: every global replacement var can be
		// modified by each procedure
		// TODO: check definition
		for (final Entry<Term, IReplacementVarOrConst> entry : mRepVarMapping.entrySet()) {
			if (entry.getValue() instanceof ReplacementNonOldVar) {
				final ReplacementNonOldVar nonOld = (ReplacementNonOldVar) entry.getValue();
				for (final String proc : mCsToolkit.getProcedures()) {
					proc2Globals.addPair(proc, nonOld);
				}
			}

		}
		return new ModifiableGlobalsTable(proc2Globals);
	}

	public boolean isUnused() {
		return mRepVarMapping.isEmpty() && mAuxVarMapping.isEmpty();
	}

}
