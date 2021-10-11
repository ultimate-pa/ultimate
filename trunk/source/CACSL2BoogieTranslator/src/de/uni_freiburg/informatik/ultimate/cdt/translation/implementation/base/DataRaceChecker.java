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
import java.util.HashMap;
import java.util.Map;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO.AUXVAR;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check.Spec;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public final class DataRaceChecker {
	private final AuxVarInfoBuilder mAuxVarInfoBuilder;
	private final MemoryHandler mMemoryHandler;

	private final Map<String, AuxVarInfo> mRaceVars = new HashMap<>();
	private final ITypeHandler mTypeHandler;

	public DataRaceChecker(final AuxVarInfoBuilder auxVarInfoBuilder, final ITypeHandler typeHandler,
			final MemoryHandler memoryHandler) {
		mAuxVarInfoBuilder = auxVarInfoBuilder;
		mTypeHandler = typeHandler;
		mMemoryHandler = memoryHandler;
	}

	public void checkOnRead(final ExpressionResultBuilder erb, final ILocation loc, final LRValue lrVal) {
		checkOnAccess(erb, loc, lrVal);
	}

	public void checkOnWrite(final ExpressionResultBuilder erb, final ILocation loc, final LRValue lrVal) {
		final AuxVarInfo tmp = checkOnAccess(erb, loc, lrVal);

		final Check check = new Check(Spec.DATA_RACE);
		final Expression formula = ExpressionFactory.and(loc,
				Arrays.stream(getRaceExpressions(loc, erb, lrVal))
						.map(expr -> ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, expr, tmp.getExp()))
						.collect(Collectors.toList()));
		final AssertStatement assertStmt = new AssertStatement(loc, formula);
		check.annotate(assertStmt);
		erb.addStatement(assertStmt);
	}

	private AuxVarInfo checkOnAccess(final ExpressionResultBuilder erb, final ILocation loc, final LRValue lrVal) {
		final ASTType boolType = new PrimitiveType(loc, BoogieType.TYPE_BOOL, "bool");
		final AuxVarInfo tmp = mAuxVarInfoBuilder.constructAuxVarInfo(loc, boolType, SFO.AUXVAR.NONDET);
		erb.addDeclaration(tmp.getVarDec());
		erb.addAuxVar(tmp);

		final HavocStatement havoc = new HavocStatement(loc, new VariableLHS[] { tmp.getLhs() });
		final LeftHandSide[] lhs = getRaceLhs(loc, erb, lrVal);
		final Expression[] exprs = new Expression[lhs.length];
		Arrays.fill(exprs, tmp.getExp());
		final AssignmentStatement assign = new AssignmentStatement(loc, lhs, exprs);
		final AtomicStatement atomic = new AtomicStatement(loc, new Statement[] { havoc, assign });
		erb.addStatement(atomic);

		return tmp;
	}

	private LeftHandSide[] getRaceLhs(final ILocation loc, final ExpressionResultBuilder erb, final LRValue lrVal) {
		if (lrVal instanceof HeapLValue) {
			final HeapLValue hlv = (HeapLValue) lrVal;
			// FIXME Probably incorrect in the presence of pointer casts; havoc "race" for every byte in memory
			return new LeftHandSide[] { new ArrayLHS(loc, mMemoryHandler.getMemoryRaceArrayLhs(loc),
					new Expression[] { hlv.getAddress() }) };
		}
		if (lrVal instanceof LocalLValue) {
			final AuxVarInfo aux = getOrCreateRaceVariable(loc, erb, (LocalLValue) lrVal);
			return new LeftHandSide[] { aux.getLhs() };
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
			final AuxVarInfo aux = getOrCreateRaceVariable(loc, erb, (LocalLValue) lrVal);
			return new Expression[] { aux.getExp() };
		}
		throw new UnsupportedOperationException();
	}

	private AuxVarInfo getOrCreateRaceVariable(final ILocation loc, final ExpressionResultBuilder erb,
			final LocalLValue lval) {
		return mRaceVars.computeIfAbsent(getKey(lval.getLhs()), x -> createRaceVariable(loc, erb));
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

	private AuxVarInfo createRaceVariable(final ILocation loc, final ExpressionResultBuilder erb) {
		final ASTType boolType = new PrimitiveType(loc, BoogieType.TYPE_BOOL, "bool");
		final AuxVarInfo aux = mAuxVarInfoBuilder.constructGlobalAuxVarInfo(loc, null, boolType, AUXVAR.RACE_DETECT);
		// erb.addAuxVar(aux);
		// erb.addDeclaration(aux.getVarDec());
		return aux;
	}

	public Collection<Declaration> declareRaceCheckingInfrastructure(final ILocation loc) {
		final ArrayList<Declaration> decl = new ArrayList<>();
		decl.add(constructMemoryRaceArrayDeclaration(loc));

		final ASTType astType = new PrimitiveType(loc, BoogieType.TYPE_BOOL, "bool");
		final VarList vlV = new VarList(loc,
				mRaceVars.values().stream().map(i -> i.getExp().getIdentifier()).toArray(String[]::new), astType);
		decl.add(new VariableDeclaration(loc, new Attribute[0], new VarList[] { vlV }));
		return decl;
	}

	private Declaration constructMemoryRaceArrayDeclaration(final ILocation loc) {
		final ASTType boolType = new PrimitiveType(loc, BoogieType.TYPE_BOOL, "bool");

		final BoogieType boogieType = BoogieType.createArrayType(0,
				new BoogieType[] { mTypeHandler.getBoogiePointerType() }, BoogieType.TYPE_BOOL);
		final ASTType astType = new ArrayType(loc, boogieType, new String[0],
				new ASTType[] { mTypeHandler.constructPointerType(loc) }, boolType);
		final VarList vlV =
				new VarList(loc, new String[] { MemoryModelDeclarations.ULTIMATE_DATA_RACE_MEMORY.getName() }, astType);
		return new VariableDeclaration(loc, new Attribute[0], new VarList[] { vlV });
	}
}
