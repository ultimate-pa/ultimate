/*
 * Copyright (C) 2014-2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2018 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO.AUXVAR;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Translates Boogie identifiers of variables and functions back to the identifiers of variables and operators in C.
 * This class is in an immature state and translates Strings to Strings.
 *
 * @author heizmann@informatik.uni-freiburg.de
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */

public class CACSL2BoogieBacktranslatorMapping implements ICACSL2BoogieBacktranslatorMapping {
	private final Map<Pair<String, DeclarationInformation>, Pair<String, CType>> mInVar2CVar;
	private final Map<Pair<String, DeclarationInformation>, Pair<String, CType>> mVar2CVar;
	private final Map<String, SFO.AUXVAR> mTempVar2Obj;
	private final Map<String, String> mFunctionId2Operator;

	public CACSL2BoogieBacktranslatorMapping() {
		mInVar2CVar = new HashMap<>();
		mVar2CVar = new HashMap<>();
		mTempVar2Obj = new HashMap<>();
		mFunctionId2Operator = new HashMap<>();
	}

	@Override
	public void putVar(final String boogieId, final String cId, final CType cType,
			final DeclarationInformation decInfo) {
		mVar2CVar.put(new Pair<>(boogieId, normalize(decInfo)), new Pair<>(cId, cType));
	}

	@Override
	public void putInVar(final String boogieId, final String cId, final CType cType,
			final DeclarationInformation decInfo) {
		mInVar2CVar.put(new Pair<>(boogieId, normalize(decInfo)), new Pair<>(cId, cType));
	}

	@Override
	public void putTempVar(final String boogieId, final SFO.AUXVAR purpose, final CType cType) {
		mTempVar2Obj.put(boogieId, purpose);
	}

	@Override
	public boolean isTempVar(final String boogieId) {
		return mTempVar2Obj.containsKey(boogieId);
	}

	boolean hasInVar(final String boogieId, final DeclarationInformation decInfo) {
		return mInVar2CVar.containsKey(new Pair<>(boogieId, normalize(decInfo)));
	}

	Pair<String, CType> getInVar(final String boogieId, final DeclarationInformation decInfo) {
		return mInVar2CVar.get(new Pair<>(boogieId, normalize(decInfo)));
	}

	boolean hasVar(final String boogieId, final DeclarationInformation decInfo) {
		return mVar2CVar.containsKey(new Pair<>(boogieId, normalize(decInfo)));
	}

	Pair<String, CType> getVar(final String boogieId, final DeclarationInformation decInfo) {
		return mVar2CVar.get(new Pair<>(boogieId, normalize(decInfo)));
	}

	Map<String, AUXVAR> getTempVar2Obj() {
		return mTempVar2Obj;
	}

	private void putFunction(final String boogieId, final String cId) {
		mFunctionId2Operator.put(boogieId, cId);
	}

	// Normalizes DeclarationInformation so that parameters of procedure implementations are identified with the
	// corresponding parameters in the procedure's declaration.
	private DeclarationInformation normalize(final DeclarationInformation decInfo) {
		switch (decInfo.getStorageClass()) {
		case IMPLEMENTATION_INPARAM:
			return new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, decInfo.getProcedure());
		case IMPLEMENTATION_OUTPARAM:
			return new DeclarationInformation(StorageClass.PROC_FUNC_OUTPARAM, decInfo.getProcedure());
		case GLOBAL:
		case IMPLEMENTATION:
		case LOCAL:
		case PROC_FUNC:
		case PROC_FUNC_INPARAM:
		case PROC_FUNC_OUTPARAM:
		case QUANTIFIED:
			return decInfo;
		}
		throw new IllegalArgumentException("unknown storage class: " + decInfo.getStorageClass());
	}
}
