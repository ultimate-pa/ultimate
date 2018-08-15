/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * {@link IdentityTransformer} is an implementation of {@link ITransformulaTransformer} that does not create new
 * {@link TransFormula}s but just passes them.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class IdentityTransformer implements ITransformulaTransformer {

	private final IIcfgSymbolTable mOldSymbolTable;
	private final ModifiableGlobalsTable mOldModifiableGlobalsTable;

	/**
	 * Default constructor.
	 *
	 * @param oldSymbolTable
	 *            The symboltable that will be returned when {@link #getNewIcfgSymbolTable()} is called.
	 */
	public IdentityTransformer(final CfgSmtToolkit oldCsToolkit) {
		mOldSymbolTable = oldCsToolkit.getSymbolTable();
		mOldModifiableGlobalsTable = oldCsToolkit.getModifiableGlobalsTable();
	}

	@Override
	public void preprocessIcfg(final IIcfg<?> icfg) {
		// no preprocessing required
	}

	@Override
	public TransformulaTransformationResult transform(final IIcfgTransition<? extends IcfgLocation> oldEdge,
			final UnmodifiableTransFormula tf) {
		return new TransformulaTransformationResult(tf);
	}

	@Override
	public String getName() {
		return IdentityTransformer.class.getSimpleName();
	}

	@Override
	public IIcfgSymbolTable getNewIcfgSymbolTable() {
		return mOldSymbolTable;
	}

	@Override
	public HashRelation<String, IProgramNonOldVar> getNewModifiedGlobals() {
		return mOldModifiableGlobalsTable.getProcToGlobals();
	}

}
