/*
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE HeapSeparator plug-in.
 *
 * The ULTIMATE HeapSeparator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE HeapSeparator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE HeapSeparator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE HeapSeparator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE HeapSeparator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.IEqualityAnalysisResultProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class NewArrayIdProvider {

	private final DefaultIcfgSymbolTable mNewSymbolTable;

	private final Map<Term, Set<Term>> mArrayIdToArrayGroup = new HashMap<>();

	private final ManagedScript mManagedScript;
	private final IIcfgSymbolTable mOldSymbolTable;
	private final HeapSeparatorBenchmark mStatistics;

	private final Map<StoreIndexInfo, IProgramNonOldVar> mArrayAccessInfoToFreezeVar;

	public NewArrayIdProvider(final CfgSmtToolkit csToolkit,
			final IEqualityAnalysisResultProvider<IcfgLocation, IIcfg<?>> equalityProvider,
			final HeapSepPreAnalysis hspav,
//			final NestedMap2<Term, EdgeInfo, IProgramNonOldVar> writeIndexTermToTfInfoToFreezeVar,
			final Map<StoreIndexInfo, IProgramNonOldVar> arrayAccessInfoToFreezeVar,
			final HeapSeparatorBenchmark statistics) {
		mManagedScript = csToolkit.getManagedScript();
		mOldSymbolTable = csToolkit.getSymbolTable();
		mNewSymbolTable = new DefaultIcfgSymbolTable(csToolkit.getSymbolTable(), csToolkit.getProcedures());
		mStatistics = statistics;
		mArrayAccessInfoToFreezeVar = arrayAccessInfoToFreezeVar;
	}



	@Override
	public String toString() {
		return "NewArrayIdProvider: \n";// + mArrayToPartitionInformation.toString();
	}

	public IIcfgSymbolTable getNewSymbolTable() {
		return mNewSymbolTable;
	}



	public Term getSubArray(final IProgramVarOrConst programVar, final List<LocationBlock> projectList) {
		// TODO Auto-generated method stub
		return null;
	}
}

