/*
 * Copyright (C) 2015-2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2017 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdgeFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class CfgSmtToolkit {

	private final ManagedScript mManagedScript;
	private final ModifiableGlobalsTable mModifiableGlobalsTable;
	private final IIcfgSymbolTable mSymbolTable;
	private final IPredicate mAxioms;
	private final OldVarsAssignmentCache mOldVarsAssignmentCache;
	private final Set<String> mProcedures;
	private final IcfgEdgeFactory mIcfgEdgeFactory;
	private final ConcurrencyInformation mConcurrencyInformation;

	public CfgSmtToolkit(final ModifiableGlobalsTable modifiableGlobalsTable, final ManagedScript managedScript,
			final IIcfgSymbolTable symbolTable, final IPredicate axioms, final Set<String> procedures,
			final IcfgEdgeFactory icfgEdgeFactory, final ConcurrencyInformation concurInfo) {
		mManagedScript = managedScript;
		mSymbolTable = symbolTable;
		mModifiableGlobalsTable = modifiableGlobalsTable;
		mOldVarsAssignmentCache = new OldVarsAssignmentCache(mManagedScript, mModifiableGlobalsTable);
		mAxioms = axioms;
		mProcedures = procedures;
		mIcfgEdgeFactory = icfgEdgeFactory;
		mConcurrencyInformation = concurInfo; 
	}

	public ManagedScript getManagedScript() {
		return mManagedScript;
	}

	public ModifiableGlobalsTable getModifiableGlobalsTable() {
		return mModifiableGlobalsTable;
	}

	public OldVarsAssignmentCache getOldVarsAssignmentCache() {
		return mOldVarsAssignmentCache;
	}

	public IIcfgSymbolTable getSymbolTable() {
		return mSymbolTable;
	}

	public IPredicate getAxioms() {
		return mAxioms;
	}

	public Set<String> getProcedures() {
		return mProcedures;
	}

	public IcfgEdgeFactory getIcfgEdgeFactory() {
		return mIcfgEdgeFactory;
	}
	
	/**
	 * Object that provides additional information about concurrency in the program.
	 * Returns null if the program is not a concurrent program.
	 */
	public ConcurrencyInformation getConcurrencyInformation() {
		return mConcurrencyInformation;
	}

}
