/*
 * Copyright (C) 2018-2019 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018-2019 University of Freiburg
 *
 * This file is part of the ULTIMATE PEAtoBoogie plug-in.
 *
 * The ULTIMATE PEAtoBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE PEAtoBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PEAtoBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PEAtoBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PEAtoBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.pea2boogie.translator;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogiePrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InitializationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InitializationPattern.VariableCategory;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.pea2boogie.IReqSymbolTable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.LinkedHashRelation;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class ReqSymboltableBuilder {

	private final ILogger mLogger;
	private final LinkedHashRelation<String, ErrorInfo> mId2Errors;
	private final Map<String, BoogieType> mId2Type;
	private final Map<String, IdentifierExpression> mId2IdExpr;
	private final Map<String, VariableLHS> mId2VarLHS;
	private final Set<String> mStateVars;
	private final Set<String> mConstVars;
	private final Set<String> mPrimedVars;
	private final Set<String> mEventVars;
	private final Set<String> mPcVars;
	private final Set<String> mClockVars;
	private final Map<String, Expression> mConst2Value;
	private final Map<String, Integer> mId2Bounds;
	private final Map<PatternType, BoogieLocation> mReq2Loc;

	public ReqSymboltableBuilder(final ILogger logger) {
		mLogger = logger;
		mId2Errors = new LinkedHashRelation<>();
		mId2Type = new LinkedHashMap<>();
		mId2IdExpr = new LinkedHashMap<>();
		mId2VarLHS = new LinkedHashMap<>();

		mStateVars = new LinkedHashSet<>();
		mConstVars = new LinkedHashSet<>();
		mPrimedVars = new LinkedHashSet<>();
		mEventVars = new LinkedHashSet<>();
		mPcVars = new LinkedHashSet<>();
		mClockVars = new LinkedHashSet<>();

		mReq2Loc = new LinkedHashMap<>();
		mConst2Value = new LinkedHashMap<>();
		mId2Bounds = new LinkedHashMap<>();

	}

	public void addInitPattern(final InitializationPattern initPattern) {
		final BoogiePrimitiveType type = toPrimitiveType(initPattern.getType());
		final String name = initPattern.getId();
		if (type == BoogieType.TYPE_ERROR) {
			addErrorError(name, new ErrorInfo(ErrorType.NONE_TYPE, initPattern));
			return;
		}

		if (initPattern.getCategory() != VariableCategory.CONST) {
			addVar(name, type, initPattern, mStateVars);
		} else {
			addVar(name, type, initPattern, mConstVars);
			mConst2Value.put(name, initPattern.getExpression());
			if (type == BoogieType.TYPE_INT || type == BoogieType.TYPE_REAL) {
				addId2Bounds(initPattern);
			}
		}
	}

	public void addPea(final PatternType pattern, final PhaseEventAutomata pea) {
		addVar(getPcName(pea), BoogieType.TYPE_INT, pattern, mPcVars);
		pea.getClocks().forEach(a -> addVar(a, BoogieType.TYPE_REAL, pattern, mClockVars));

		for (final Entry<String, String> entry : pea.getVariables().entrySet()) {
			final String name = entry.getKey();
			final String type = entry.getValue();

			if (type == null) {
				checkVar(name, pattern);
				continue;
			}

			switch (type.toLowerCase()) {
			case "bool":
			case "real":
			case "int":
				addVar(name, toPrimitiveType(type), pattern, mStateVars);
				break;
			case "event":
				addVar(name, BoogieType.TYPE_BOOL, pattern, mEventVars);
				break;
			default:
				addErrorError(name, new ErrorInfo(ErrorType.UNKNOWN_TYPE, pattern));
				break;
			}
		}
	}

	public IReqSymbolTable constructSymbolTable() {
		final String deltaVar = declareDeltaVar();
		return new ReqSymbolTable(deltaVar, mId2Type, mId2IdExpr, mId2VarLHS, mStateVars, mPrimedVars, mConstVars,
				mEventVars, mPcVars, mClockVars, mReq2Loc, mConst2Value);
	}

	public Set<String> getConstIds() {
		return mConstVars;
	}

	public Map<String, Integer> getId2Bounds() {
		return mId2Bounds;
	}

	public Set<Entry<String, ErrorInfo>> getErrors() {
		return Collections.unmodifiableSet(mId2Errors.entrySet());
	}

	private void addErrorError(final String name, final ErrorInfo typeErrorInfo) {
		if (mId2Errors.addPair(name, typeErrorInfo)) {
			mLogger.error(typeErrorInfo.mType + " for " + name);
		}
	}

	private void addId2Bounds(final InitializationPattern init) {

		final Expression expr = init.getExpression();
		final Integer val;
		if (expr instanceof RealLiteral) {
			val = tryParseInt(init, ((RealLiteral) expr).getValue());
		} else if (expr instanceof IntegerLiteral) {
			val = tryParseInt(init, ((IntegerLiteral) expr).getValue());
		} else {
			val = null;
			addErrorError(init.getId(), new ErrorInfo(ErrorType.SYNTAX_ERROR, init,
					"Cannot convert CONST with expression " + BoogiePrettyPrinter.print(expr) + " to duration"));
		}
		if (val == null) {
			return;
		}
		mId2Bounds.put(init.getId(), val);
	}

	private Integer tryParseInt(final PatternType pattern, final String val) {
		try {
			return new BigDecimal(val).toBigIntegerExact().intValueExact();
		} catch (final NumberFormatException ex) {
			addErrorError(pattern.getId(),
					new ErrorInfo(ErrorType.SYNTAX_ERROR, pattern, "Cannot convert CONST with value " + val
							+ " to duration (must be integer literal or non-fractional real literal)"));
			return null;
		} catch (final ArithmeticException ex) {
			return null;
		}
	}

	private void addVar(final String name, final BoogieType type, final PatternType source, final Set<String> kind) {
		if (type == null && (!kind.contains(name) || !mId2Type.containsKey(name))) {
			throw new AssertionError();
		}

		if (kind != null) {
			kind.add(name);
		}

		final BoogieType old = mId2Type.put(name, type);
		if (old != null && old != type) {
			addErrorError(name, new ErrorInfo(ErrorType.DUPLICATE_DECLARATION, source));
			mId2Type.put(name, BoogieType.TYPE_ERROR);
			return;
		}

		final ILocation loc = getLocation(source);
		final IdentifierExpression idExpr = ExpressionFactory.constructIdentifierExpression(loc, type, name,
				DeclarationInformation.DECLARATIONINFO_GLOBAL);
		mId2IdExpr.put(name, idExpr);
		mId2VarLHS.put(name, new VariableLHS(loc, name));
		if (source instanceof InitializationPattern
				&& ((InitializationPattern) source).getCategory() == VariableCategory.CONST) {
			// consts do not need primed variables
			return;
		}
		if (mPrimedVars.contains(name)) {
			return;
		}
		addVar(getPrimedVarId(name), type, source, mPrimedVars);
	}

	private void checkVar(final String name, final PatternType source) {
		if (mId2Type.containsKey(name)) {
			return;
		}
		addErrorError(name, new ErrorInfo(ErrorType.MISSING_DECLARATION, source));
	}

	private ILocation getLocation(final PatternType source) {
		// TODO: Fix locations
		final ILocation loc = mReq2Loc.get(source);
		if (loc != null) {
			return loc;
		}
		final BoogieLocation newLoc = new BoogieLocation("", -1, -1, -1, -1);
		mReq2Loc.put(source, newLoc);
		return newLoc;
	}

	private String declareDeltaVar() {
		// declare delta var
		String name = "delta";
		while (mId2Type.containsKey(name)) {
			name = "_" + name;
		}

		addVar(name, BoogieType.TYPE_REAL, null, null);
		return name;
	}

	private static BoogiePrimitiveType toPrimitiveType(final String type) {
		switch (type.toLowerCase()) {
		case "bool":
			return BoogieType.TYPE_BOOL;
		case "real":
			return BoogieType.TYPE_REAL;
		case "int":
			return BoogieType.TYPE_INT;
		default:
			return BoogieType.TYPE_ERROR;
		}
	}

	private static String getPrimedVarId(final String name) {
		return name + "'";
	}

	private static String getPcName(final PhaseEventAutomata aut) {
		return aut.getName() + "_pc";
	}

	private static final class ReqSymbolTable implements IReqSymbolTable {

		private static final Attribute[] EMPTY_ATTRIBUTES = new Attribute[0];
		private final Map<String, BoogieType> mId2Type;
		private final Map<String, IdentifierExpression> mId2IdExpr;
		private final Map<String, VariableLHS> mId2VarLHS;
		private final Map<String, Expression> mConst2Value;
		private final Map<PatternType, BoogieLocation> mReq2Loc;
		private final Set<String> mStateVars;
		private final Set<String> mConstVars;
		private final Set<String> mPrimedVars;
		private final Set<String> mEventVars;
		private final Set<String> mPcVars;
		private final Set<String> mClockVars;
		private final String mDeltaVar;

		private ReqSymbolTable(final String deltaVar, final Map<String, BoogieType> id2Type,
				final Map<String, IdentifierExpression> id2idExp, final Map<String, VariableLHS> id2VarLhs,
				final Set<String> stateVars, final Set<String> primedVars, final Set<String> constVars,
				final Set<String> eventVars, final Set<String> pcVars, final Set<String> clockVars,
				final Map<PatternType, BoogieLocation> req2loc, final Map<String, Expression> const2Value) {
			mId2Type = Collections.unmodifiableMap(id2Type);
			mId2IdExpr = Collections.unmodifiableMap(id2idExp);
			mId2VarLHS = Collections.unmodifiableMap(id2VarLhs);

			mStateVars = Collections.unmodifiableSet(stateVars);
			mConstVars = Collections.unmodifiableSet(constVars);
			mPrimedVars = Collections.unmodifiableSet(primedVars);
			mEventVars = Collections.unmodifiableSet(eventVars);
			mPcVars = Collections.unmodifiableSet(pcVars);
			mClockVars = Collections.unmodifiableSet(clockVars);
			mReq2Loc = Collections.unmodifiableMap(req2loc);
			mConst2Value = Collections.unmodifiableMap(const2Value);
			mDeltaVar = deltaVar;
		}

		@Override
		public IdentifierExpression getIdentifierExpression(final String name) {
			final IdentifierExpression idExpr = mId2IdExpr.get(name);
			if (idExpr == null || idExpr.getType() == null) {
				throw new AssertionError(name + " has no identifier expression or no type");
			}
			assert idExpr != null && idExpr.getType() != null;
			return idExpr;
		}

		@Override
		public Map<PatternType, BoogieLocation> getLocations() {
			return Collections.unmodifiableMap(mReq2Loc);
		}

		@Override
		public String getDeltaVarName() {
			return mDeltaVar;
		}

		@Override
		public VariableLHS getVariableLhs(final String id) {
			return mId2VarLHS.get(id);
		}

		@Override
		public Set<String> getStateVars() {
			return mStateVars;
		}

		@Override
		public Set<String> getPrimedVars() {
			return mPrimedVars;
		}

		@Override
		public Set<String> getEventVars() {
			return mEventVars;
		}

		@Override
		public Set<String> getClockVars() {
			return mClockVars;
		}

		@Override
		public Set<String> getPcVars() {
			return mPcVars;
		}

		@Override
		public Set<String> getConstVars() {
			return mConstVars;
		}

		@Override
		public Map<String, Expression> getConstToValue() {
			return mConst2Value;
		}

		@Override
		public String getPcName(final PhaseEventAutomata automaton) {
			return ReqSymboltableBuilder.getPcName(automaton);
		}

		@Override
		public String getPrimedVarId(final String name) {
			return ReqSymboltableBuilder.getPrimedVarId(name);
		}

		@Override
		public Collection<? extends Declaration> getDeclarations() {
			final List<Declaration> decls = new ArrayList<>();
			decls.add(constructVariableDeclaration(getDeltaVarName()));
			decls.addAll(constructVariableDeclarations(mClockVars));
			decls.addAll(constructVariableDeclarations(mPcVars));
			decls.addAll(constructConstDeclarations(mConstVars));
			decls.addAll(constructVariableDeclarations(mStateVars));
			decls.addAll(constructVariableDeclarations(mPrimedVars));
			decls.addAll(constructVariableDeclarations(mEventVars));
			return decls;
		}

		private List<Declaration> constructVariableDeclarations(final Collection<String> identifiers) {
			final List<? extends VarList> varlist = constructVarLists(identifiers);
			return varlist.stream()
					.map(a -> new VariableDeclaration(a.getLocation(), EMPTY_ATTRIBUTES, new VarList[] { a }))
					.collect(Collectors.toList());
		}

		private List<Declaration> constructConstDeclarations(final Collection<String> identifiers) {
			final List<? extends VarList> varlists = constructVarLists(identifiers);
			final List<Declaration> rtr = new ArrayList<>();
			// add constant declarations
			varlists.stream().map(a -> new ConstDeclaration(a.getLocation(), EMPTY_ATTRIBUTES, false, a, null, false))
					.forEachOrdered(rtr::add);
			// add axiom for each constant
			for (final VarList varlist : varlists) {
				for (final String id : varlist.getIdentifiers()) {
					final Expression value = mConst2Value.get(id);
					final IdentifierExpression idExpr = mId2IdExpr.get(id);
					final Expression axiom =
							new BinaryExpression(value.getLoc(), value.getType(), Operator.COMPEQ, idExpr, value);
					rtr.add(new Axiom(varlist.getLocation(), EMPTY_ATTRIBUTES, axiom));
				}
			}
			return rtr;
		}

		private Declaration constructVariableDeclaration(final String identifier) {
			final VarList varlist = constructVarlist(identifier);
			if (varlist == null) {
				return null;
			}
			return new VariableDeclaration(varlist.getLocation(), EMPTY_ATTRIBUTES, new VarList[] { varlist });
		}

		private VarList constructVarlist(final String identifier) {
			final BoogieType type = mId2Type.get(identifier);
			final IdentifierExpression idExpr = mId2IdExpr.get(identifier);
			if (type == null || idExpr == null) {
				return null;
			}
			return new VarList(idExpr.getLocation(), new String[] { identifier }, type.toASTType(idExpr.getLocation()));
		}

		private List<? extends VarList> constructVarLists(final Collection<String> identifiers) {
			if (identifiers.isEmpty()) {
				return Collections.emptyList();
			}
			return identifiers.stream().map(this::constructVarlist).filter(a -> a != null).collect(Collectors.toList());
		}

	}

	public enum ErrorType {
		DUPLICATE_DECLARATION, UNKNOWN_TYPE, NO_DURATION_EXPRESSION, NO_DURATION_VALUE, NONE_TYPE, MISSING_DECLARATION,
		SYNTAX_ERROR
	}

	public static final class ErrorInfo {

		private final ErrorType mType;
		private final PatternType mSource;
		private final String mMessage;

		public ErrorInfo(final ErrorType type, final PatternType req) {
			mType = type;
			mSource = req;
			mMessage = null;
		}

		public ErrorInfo(final ErrorType type, final PatternType req, final String message) {
			mType = type;
			mSource = req;
			mMessage = message;
		}

		public PatternType getSource() {
			return mSource;
		}

		public ErrorType getType() {
			return mType;
		}

		public String getMessage() {
			return mMessage;
		}

	}

}
