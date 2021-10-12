/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler.MemoryModelDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check.Spec;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public final class DataRaceChecker {
	private final AuxVarInfoBuilder mAuxVarInfoBuilder;
	private final MemoryHandler mMemoryHandler;

	private final Set<String> mRaceVars = new HashSet<>();
	private final ITypeHandler mTypeHandler;

	public DataRaceChecker(final AuxVarInfoBuilder auxVarInfoBuilder, final ITypeHandler typeHandler,
			final MemoryHandler memoryHandler) {
		mAuxVarInfoBuilder = auxVarInfoBuilder;
		mTypeHandler = typeHandler;
		mMemoryHandler = memoryHandler;
	}

	public void checkOnRead(final ExpressionResultBuilder erb, final ILocation loc, final LRValue lrVal) {
		if (!isRaceImpossible(lrVal)) {
			checkOnAccess(erb, loc, lrVal);
		}
	}

	public void checkOnWrite(final ExpressionResultBuilder erb, final ILocation loc, final LRValue lrVal) {
		if (isRaceImpossible(lrVal)) {
			return;
		}

		final AuxVarInfo tmp = checkOnAccess(erb, loc, lrVal);

		final Check check = new Check(Spec.DATA_RACE);
		final Expression formula = ExpressionFactory.and(loc,
				Arrays.stream(getRaceExpressions(loc, erb, lrVal))
						.map(expr -> ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, expr, tmp.getExp()))
						.collect(Collectors.toList()));
		final Statement assertStmt = new AssertStatement(loc, formula);
		check.annotate(assertStmt);
		erb.addStatement(assertStmt);
	}

	private AuxVarInfo checkOnAccess(final ExpressionResultBuilder erb, final ILocation loc, final LRValue lrVal) {
		final AuxVarInfo tmp = mAuxVarInfoBuilder.constructAuxVarInfo(loc, getBoolASTType(), SFO.AUXVAR.NONDET);
		erb.addDeclaration(tmp.getVarDec());
		erb.addAuxVar(tmp);
		final Statement havoc = new HavocStatement(loc, new VariableLHS[] { tmp.getLhs() });

		final LeftHandSide[] lhs = getRaceLhs(loc, erb, lrVal);
		final Expression[] exprs = new Expression[lhs.length];
		Arrays.fill(exprs, tmp.getExp());
		final Statement assign = StatementFactory.constructAssignmentStatement(loc, lhs, exprs);

		final Statement atomic = new AtomicStatement(loc, new Statement[] { havoc, assign });
		erb.addStatement(atomic);

		return tmp;
	}

	private static boolean isRaceImpossible(final LRValue lrVal) {
		if (!(lrVal instanceof LocalLValue)) {
			return false;
		}
		final LocalLValue locLv = (LocalLValue) lrVal;
		if (!(locLv.getLhs() instanceof VariableLHS)) {
			return false;
		}
		final VariableLHS varLhs = (VariableLHS) locLv.getLhs();
		final StorageClass storageCls = varLhs.getDeclarationInformation().getStorageClass();
		return storageCls == StorageClass.LOCAL || storageCls == StorageClass.IMPLEMENTATION_INPARAM
				|| storageCls == StorageClass.IMPLEMENTATION_OUTPARAM || storageCls == StorageClass.PROC_FUNC;
	}

	private LeftHandSide[] getRaceLhs(final ILocation loc, final ExpressionResultBuilder erb, final LRValue lrVal) {
		if (lrVal instanceof HeapLValue) {
			final HeapLValue hlv = (HeapLValue) lrVal;
			// FIXME Probably incorrect in the presence of pointer casts; havoc "race" for every byte in memory
			return new LeftHandSide[] { ExpressionFactory.constructNestedArrayLHS(loc,
					mMemoryHandler.getMemoryRaceArrayLhs(loc), new Expression[] { hlv.getAddress() }) };
		}
		if (lrVal instanceof LocalLValue) {
			return new LeftHandSide[] { getRaceVariableLhs(loc, erb, (LocalLValue) lrVal) };
		}
		throw new UnsupportedOperationException();
	}

	private Expression[] getRaceExpressions(final ILocation loc, final ExpressionResultBuilder erb,
			final LRValue lrVal) {
		if (lrVal instanceof HeapLValue) {
			final HeapLValue hlv = (HeapLValue) lrVal;
			// FIXME Probably incorrect in the presence of pointer casts; check "race" for every byte in memory
			return new Expression[] { ExpressionFactory.constructNestedArrayAccessExpression(loc,
					mMemoryHandler.getMemoryRaceArray(loc), new Expression[] { hlv.getAddress() }) };
		}
		if (lrVal instanceof LocalLValue) {
			return new Expression[] { getRaceVariableExpression(loc, erb, (LocalLValue) lrVal) };
		}
		throw new UnsupportedOperationException();
	}

	private Expression getRaceVariableExpression(final ILocation loc, final ExpressionResultBuilder erb,
			final LocalLValue lval) {
		return ExpressionFactory.constructIdentifierExpression(loc, getBoolType(), getRaceVariableName(lval.getLhs()),
				DeclarationInformation.DECLARATIONINFO_GLOBAL);
	}

	private VariableLHS getRaceVariableLhs(final ILocation loc, final ExpressionResultBuilder erb,
			final LocalLValue lval) {
		return ExpressionFactory.constructVariableLHS(loc, getBoolType(), getRaceVariableName(lval.getLhs()),
				DeclarationInformation.DECLARATIONINFO_GLOBAL);
	}

	private String getRaceVariableName(final LeftHandSide lhs) {
		final String name = "#race" + getKey(lhs);
		mRaceVars.add(name);
		return name;
	}

	private String getKey(final LeftHandSide lhs) {
		if (lhs instanceof VariableLHS) {
			return ((VariableLHS) lhs).getIdentifier();
		}
		if (lhs instanceof StructLHS) {
			return getKey(((StructLHS) lhs).getStruct()) + "." + ((StructLHS) lhs).getField();
		}
		throw new UnsupportedOperationException();
	}

	public Collection<Declaration> declareRaceCheckingInfrastructure(final ILocation loc) {
		final ArrayList<Declaration> decl = new ArrayList<>();
		decl.add(constructMemoryRaceArrayDeclaration(loc));

		final VarList vlV = new VarList(loc, mRaceVars.toArray(String[]::new), getBoolASTType());
		decl.add(new VariableDeclaration(loc, new Attribute[0], new VarList[] { vlV }));
		return decl;
	}

	private Declaration constructMemoryRaceArrayDeclaration(final ILocation loc) {
		final BoogieType boogieType =
				BoogieType.createArrayType(0, new BoogieType[] { mTypeHandler.getBoogiePointerType() }, getBoolType());
		final ASTType astType = new ArrayType(loc, boogieType, new String[0],
				new ASTType[] { mTypeHandler.constructPointerType(loc) }, getBoolASTType());
		final VarList vlV =
				new VarList(loc, new String[] { MemoryModelDeclarations.ULTIMATE_DATA_RACE_MEMORY.getName() }, astType);
		return new VariableDeclaration(loc, new Attribute[0], new VarList[] { vlV });
	}

	private ASTType getBoolASTType() {
		return mMemoryHandler.getBooleanArrayHelper().constructBoolReplacementType();
	}

	private BoogieType getBoolType() {
		return mTypeHandler.getBoogieTypeForBoogieASTType(getBoolASTType());
	}
}
