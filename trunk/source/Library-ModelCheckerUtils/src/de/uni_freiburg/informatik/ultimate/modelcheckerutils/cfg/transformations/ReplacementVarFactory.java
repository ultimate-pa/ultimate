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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ConstantFinder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Factory for constructing ReplacementVars ensures that for each defining
 * Term exactly one ReplacementVar is constructed.
 * @author Matthias Heizmann
 *
 */
public class ReplacementVarFactory {
	
	private final ManagedScript mMgdScript;
	private final IIcfgSymbolTable mIIcfgSymbolTable;
	private final Map<Term, IReplacementVarOrConst> mRepVarMapping = new HashMap<>();
	private final Map<String, TermVariable> mAuxVarMapping = new HashMap<>();
	private final boolean mUseIntraproceduralReplacementVars = true;

	public ReplacementVarFactory(final ManagedScript mgdScript, final IIcfgSymbolTable symbolTable) {
		super();
		mMgdScript = mgdScript;
		mIIcfgSymbolTable = symbolTable;
	}

	/**
	 * Get the ReplacementVar that is used as a replacement for the Term
	 * definition. Construct this ReplacementVar if it does not exist yet.
	 */
	public IReplacementVarOrConst getOrConstuctReplacementVar(final Term definition) {
		final IReplacementVarOrConst repVar = mRepVarMapping.get(definition);
		if (repVar != null) {
			return repVar;
		} else {
			final IReplacementVarOrConst newRepVar;
			final String nameCandidate = "rep" + SmtUtils.removeSmtQuoteCharacters(definition.toString());
			final TermVariable tv = mMgdScript.constructFreshTermVariable(nameCandidate, definition.getSort());
			final String name = tv.getName();
			
			final Pair<Set<Class<? extends IProgramVarOrConst>>, Set<String>> analysisResult = analyzeDefinition(definition);
			if (analysisResult.getFirst().contains(IProgramNonOldVar.class) && analysisResult.getFirst().contains(IProgramOldVar.class)) {
				throw new UnsupportedOperationException("nonold and old");
				// construct intraprocedural
				// newRepVar = new ReplacementVar(definition.toString(), definition, tv);
			} else if (analysisResult.getFirst().contains(ILocalProgramVar.class)) {
				if (analysisResult.getSecond().size() > 1) {
					throw new UnsupportedOperationException("more than one procedure");
					// construct intraprocedural
					// newRepVar = new ReplacementVar(definition.toString(), definition, tv);
				} else {
					final String proc = analysisResult.getSecond().iterator().next();
					mMgdScript.lock(this);
					final ApplicationTerm defaultConstant = ProgramVarUtils.constructDefaultConstant(
							mMgdScript, this, tv.getSort(), name);
					final ApplicationTerm primedContant = ProgramVarUtils.constructPrimedConstant(
							mMgdScript, this, tv.getSort(), name);
					mMgdScript.unlock(this);
					newRepVar = new LocalReplacementVar(name, proc, tv, defaultConstant, primedContant, definition);
				} 
			} else if (analysisResult.getFirst().contains(IProgramNonOldVar.class)) {
				newRepVar = new ReplacementVar(definition.toString(), definition, tv);
			} else if (analysisResult.getFirst().contains(IProgramOldVar.class)) {
				newRepVar = new ReplacementVar(definition.toString(), definition, tv);
			} else {
//				mMgdScript.lock(this);
//				mMgdScript.declareFun(this, name, new Sort[0], tv.getSort());
//				mMgdScript.unlock(this);
//				final ApplicationTerm smtConstant = (ApplicationTerm) mMgdScript.term(this, name);
//				newRepVar = new ReplacementConst(name, smtConstant, definition);
				newRepVar = new ReplacementVar(definition.toString(), definition, tv);
			}
			mRepVarMapping.put(definition, newRepVar);
			return newRepVar;
		}
		
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
		final Pair<Set<Class<? extends IProgramVarOrConst>>,Set<String>> result = new Pair<>(constOrVarKinds, procs);
		for (final TermVariable tv : definition.getFreeVars()) {
			final IProgramVar pv = mIIcfgSymbolTable.getProgramVar(tv);
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
		return result;
	}
	
}
