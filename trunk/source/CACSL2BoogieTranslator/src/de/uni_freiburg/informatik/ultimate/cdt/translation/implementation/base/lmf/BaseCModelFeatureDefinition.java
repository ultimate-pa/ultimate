/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.lmf;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public abstract class BaseCModelFeatureDefinition implements ICModelFeatureDefinition {

	/**
	 * Add also implementations of malloc, free, write and read functions. TODO: details
	 */
	protected static final boolean ADD_IMPLEMENTATIONS = false;

	/**
	 * The "~addr" variable identifier.
	 */
	protected static final String ADDR = "~addr";

}

// class MemoryModelDeclarationInfo {
//
// private final MemoryModelDeclarations mMmd;
// private final BoogieType mBoogieType;
//
// public MemoryModelDeclarationInfo(final MemoryModelDeclarations mmd) {
// mMmd = mmd;
// mBoogieType = null;
// }
//
// public MemoryModelDeclarationInfo(final MemoryModelDeclarations mmd, final BoogieType boogieType) {
// mMmd = mmd;
// mBoogieType = boogieType;
// }
//
// IdentifierExpression constructIdentiferExpression(final ILocation loc) {
// return ExpressionFactory.constructIdentifierExpression(loc, mBoogieType, mMmd.getName(),
// DeclarationInformation.DECLARATIONINFO_GLOBAL);
// }
//
// VariableLHS constructVariableLHS(final ILocation loc) {
// return ExpressionFactory.constructVariableLHS(loc, mBoogieType, mMmd.getName(),
// DeclarationInformation.DECLARATIONINFO_GLOBAL);
// }
//
// BoogieType getBoogieType() {
// if (mBoogieType == null) {
// throw new IllegalStateException();
// }
// return mBoogieType;
// }
// }

// private MemoryModelDeclarationInfo constructMemoryModelDeclarationInfo(final MemoryModelDeclarations mmd) {
// switch (mmd) {
// case C_MEMCPY:
// break;
// case C_MEMMOVE:
// break;
// case C_MEMSET:
// break;
// case ULTIMATE_ALLOC:
// break;
// case ULTIMATE_DEALLOC:
// break;
// case ULTIMATE_LENGTH:
// return new MemoryModelDeclarationInfo(mmd, BoogieType.createArrayType(0,
// new BoogieType[] { mTypeHandler.getBoogieTypeForPointerComponents() }, BoogieType.TYPE_INT));
// case ULTIMATE_MEMINIT:
// break;
// case ULTIMATE_PTHREADS_MUTEX:
// return new MemoryModelDeclarationInfo(mmd,
// BoogieType.createArrayType(0, new BoogieType[] { mTypeHandler.getBoogiePointerType() }, mTypeHandler
// .getBoogieTypeForBoogieASTType(getBooleanArrayHelper().constructBoolReplacementType())));
// case ULTIMATE_VALID:
// return new MemoryModelDeclarationInfo(mmd,
// BoogieType.createArrayType(0, new BoogieType[] { mTypeHandler.getBoogieTypeForPointerComponents() },
// mTypeHandler.getBoogieTypeForBoogieASTType(
// getBooleanArrayHelper().constructBoolReplacementType())));
// case ULTIMATE_STACK_HEAP_BARRIER:
// return new MemoryModelDeclarationInfo(mmd, mTypeHandler.getBoogieTypeForPointerComponents());
// default:
// break;
// }
// // construct empty mmdi
// return new MemoryModelDeclarationInfo(mmd);
// }