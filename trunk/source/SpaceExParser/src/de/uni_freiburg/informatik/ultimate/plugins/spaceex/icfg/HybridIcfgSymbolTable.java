/*
 * Copyright (C) 2017 Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE SpaceExParser plug-in.
 *
 * The ULTIMATE SpaceExParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SpaceExParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SpaceExParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SpaceExParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SpaceExParser plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.spaceex.icfg;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.HybridAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.util.HybridTranslatorConstants;

/**
 * Class that implements an IIcfgSymbolTable
 *
 * @author Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 *
 */
public class HybridIcfgSymbolTable implements IIcfgSymbolTable {

	private final Map<String, Set<ILocalProgramVar>> mLocals;
	private final Map<TermVariable, ILocalProgramVar> mTVtoProgVar;

	/**
	 * Constructor
	 *
	 * @param script
	 * @param automaton
	 * @param binds
	 */
	public HybridIcfgSymbolTable(final ManagedScript script, final HybridAutomaton automaton, final String procedure,
			final HybridVariableManager variableManager) {
		mLocals = new HashMap<>();
		mTVtoProgVar = new HashMap<>();

		final Set<String> variables = automaton.getGlobalParameters();
		variables.addAll(automaton.getGlobalConstants());
		variables.addAll(automaton.getLocalConstants());
		variables.addAll(automaton.getLocalParameters());
		variables.add(HybridTranslatorConstants.TIME_VAR);

		final Set<ILocalProgramVar> progVars = new HashSet<>();
		final Sort realSort = SmtSortUtils.getRealSort(script);
		for (final String var : variables) {
			// Termvariables for the transformula.
			final TermVariable inVar = script.constructFreshTermVariable(var, realSort);
			final TermVariable outVar = script.constructFreshTermVariable(var, realSort);
			// IProgramVar for the transformula.
			final HybridProgramVar progVar = variableManager.constructProgramVar(var, procedure);
			if (!var.equals(HybridTranslatorConstants.TIME_VAR)) {
				variableManager.addInVarTermVariable(var, inVar);
				variableManager.addOutVarTermVariable(var, outVar);
				variableManager.addProgramVar(var, progVar);
				mTVtoProgVar.put(inVar, progVar);
				mTVtoProgVar.put(outVar, progVar);
				progVars.add(progVar);
			}
		}
		mLocals.put(procedure, progVars);
	}

	@Override
	public Set<ILocalProgramVar> getLocals(final String procedurename) {
		return mLocals.get(procedurename);
	}

	@Override
	public Set<IProgramNonOldVar> getGlobals() {
		return Collections.emptySet();
	}

	@Override
	public Set<IProgramConst> getConstants() {
		return Collections.emptySet();
	}

	@Override
	public IProgramVar getProgramVar(final TermVariable tv) {
		return mTVtoProgVar.get(tv);
	}

	@Override
	public IProgramConst getProgramConst(final ApplicationTerm at) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Set<ApplicationTerm> computeAllDefaultConstants() {
		throw new UnsupportedOperationException("Not yet implemented");
	}

}
