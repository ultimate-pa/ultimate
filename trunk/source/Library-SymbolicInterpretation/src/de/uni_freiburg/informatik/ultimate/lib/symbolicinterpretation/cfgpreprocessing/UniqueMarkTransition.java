/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-SymbolicInterpretation plug-in.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-SymbolicInterpretation plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-SymbolicInterpretation plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-SymbolicInterpretation plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.cfgpreprocessing;

import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.regexdag.RegexDag;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.regexdag.RegexDagCompressor;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;

/**
 * Pure marker, for instance for locations of interest (LOI) inside {@link RegexDag}
 * This class does not overwrite equals so that all objects of this class are unique
 * and cannot be merged by {@link RegexDagCompressor}.
 * 
 * @author schaetzc@tf.uni-freiburg.de
 */
public class UniqueMarkTransition implements IIcfgInternalTransition<IcfgLocation> {

	private static final long serialVersionUID = 3983599864540967953L;

	private final IcfgLocation mTransition;

	public UniqueMarkTransition(final IcfgLocation loi) {
		mTransition = loi;
	}

	@Override
	public IcfgLocation getSource() {
		throw new UnsupportedOperationException();
	}

	@Override
	public IcfgLocation getTarget() {
		return mTransition;
	}

	@Override
	public IPayload getPayload() {
		return null;
	}

	@Override
	public boolean hasPayload() {
		return false;
	}

	@Override
	public String getPrecedingProcedure() {
		throw new UnsupportedOperationException();
	}

	@Override
	public String getSucceedingProcedure() {
		throw new UnsupportedOperationException();
	}

	@Override
	public UnmodifiableTransFormula getTransformula() {
		throw new UnsupportedOperationException();
	}

	@Override
	public String toString() {
		return mTransition.toString();
	}
}
