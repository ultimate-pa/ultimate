/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE BuchiAutomizer plug-in.
 *
 * The ULTIMATE BuchiAutomizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BuchiAutomizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BuchiAutomizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BuchiAutomizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BuchiAutomizer plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Constructs auxiliary variables that store the old value of a ranking function (oldRank) and that store if we already
 * check for decreases of the ranking function (unseeded).
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class RankVarConstructor {
	public static final String UNSEEDED_IDENTIFIER = "unseeded";
	public static final String OLD_RANK_IDENTIFIER = "oldRank";
	public static final int MAX_LEX_COMPONENTS = 7;

	private final ManagedScript mManagedScript;
	private final IProgramNonOldVar mUnseededVariable;
	private final IProgramNonOldVar[] mOldRankVariables;

	private final CfgSmtToolkit mCfgSmtToolkitWithRankVariables;

	public RankVarConstructor(final CfgSmtToolkit csToolkit) {
		mManagedScript = csToolkit.getManagedScript();

		final DefaultIcfgSymbolTable newSymbolTable =
				new DefaultIcfgSymbolTable(csToolkit.getSymbolTable(), csToolkit.getProcedures());

		mManagedScript.lock(newSymbolTable);

		final Sort boolSort = SmtSortUtils.getBoolSort(csToolkit.getManagedScript());
		mUnseededVariable = ProgramVarUtils.constructGlobalProgramVarPair(UNSEEDED_IDENTIFIER, boolSort,
				csToolkit.getManagedScript(), newSymbolTable);
		newSymbolTable.add(mUnseededVariable);

		mOldRankVariables = new IProgramNonOldVar[MAX_LEX_COMPONENTS];
		final Sort intSort = SmtSortUtils.getIntSort(csToolkit.getManagedScript());
		for (int i = 0; i < MAX_LEX_COMPONENTS; i++) {
			final String name = OLD_RANK_IDENTIFIER + i;
			mOldRankVariables[i] = ProgramVarUtils.constructGlobalProgramVarPair(name, intSort,
					csToolkit.getManagedScript(), newSymbolTable);
			newSymbolTable.add(mOldRankVariables[i]);
		}
		mManagedScript.unlock(newSymbolTable);

		final HashRelation<String, IProgramNonOldVar> proc2globals = new HashRelation<>();
		for (final String proc : csToolkit.getProcedures()) {
			for (final IProgramNonOldVar nonOld : csToolkit.getModifiableGlobalsTable().getModifiedBoogieVars(proc)) {
				proc2globals.addPair(proc, nonOld);
			}
			proc2globals.addPair(proc, mUnseededVariable);
			for (final IProgramNonOldVar oldRankVar : mOldRankVariables) {
				proc2globals.addPair(proc, oldRankVar);
			}
		}
		final ModifiableGlobalsTable modifiableGlobalsTable = new ModifiableGlobalsTable(proc2globals);
		mCfgSmtToolkitWithRankVariables = new CfgSmtToolkit(modifiableGlobalsTable, csToolkit.getManagedScript(),
				newSymbolTable, csToolkit.getProcedures(), csToolkit.getInParams(), csToolkit.getOutParams(),
				csToolkit.getIcfgEdgeFactory(), csToolkit.getConcurrencyInformation(), csToolkit.getSmtSymbols());
	}

	/**
	 * @return the unseededVariable
	 */
	public IProgramNonOldVar getUnseededVariable() {
		return mUnseededVariable;
	}

	/**
	 * @return the oldRankVariables
	 */
	public IProgramNonOldVar[] getOldRankVariables() {
		return mOldRankVariables;
	}

	public CfgSmtToolkit getCsToolkitWithRankVariables() {
		return mCfgSmtToolkitWithRankVariables;
	}

}
