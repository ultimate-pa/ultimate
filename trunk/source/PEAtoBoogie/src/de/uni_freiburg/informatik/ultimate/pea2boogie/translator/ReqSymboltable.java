package de.uni_freiburg.informatik.ultimate.pea2boogie.translator;

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
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogiePrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InitializationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InitializationPattern.VariableCategory;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.pea2boogie.IReqSymbolExpressionTable;

public class ReqSymboltable implements IReqSymbolExpressionTable {

	private static final Attribute[] EMPTY_ATTRIBUTES = new Attribute[0];

	private final Map<String, TypeErrorInfo> mId2TypeErrors;
	private final Map<String, BoogieType> mId2Type;
	private final Map<String, IdentifierExpression> mId2IdExpr;
	private final Map<String, VariableLHS> mId2VarLHS;

	private final Map<PatternType, BoogieLocation> mReq2Loc;

	private final Set<String> mStateVars;
	private final Set<String> mConstVars;
	private final Set<String> mPrimedVars;
	private final Set<String> mEventVars;
	private final Set<String> mPcVars;
	private final Set<String> mClockVars;

	private final ILogger mLogger;

	private final String mDeltaVar;

	public ReqSymboltable(final ILogger logger, final Map<PatternType, PhaseEventAutomata> req2Automata,
			final List<InitializationPattern> inits) {
		mId2Type = new LinkedHashMap<>();
		mId2IdExpr = new LinkedHashMap<>();
		mId2TypeErrors = new LinkedHashMap<>();
		mId2VarLHS = new LinkedHashMap<>();
		mStateVars = new LinkedHashSet<>();
		mConstVars = new LinkedHashSet<>();
		mPrimedVars = new LinkedHashSet<>();
		mEventVars = new LinkedHashSet<>();
		mPcVars = new LinkedHashSet<>();
		mClockVars = new LinkedHashSet<>();
		mReq2Loc = new LinkedHashMap<>();

		mLogger = logger;

		// extract state vars from init pattern
		extractVariablesFromInit(inits);

		// extract pcid vars, clock vars, state vars, primed state vars, and event vars
		extractVariablesFromAutomata(req2Automata);

		mDeltaVar = declareDeltaVar();
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

	private void extractVariablesFromInit(final List<InitializationPattern> inits) {
		for (final InitializationPattern init : inits) {
			final BoogiePrimitiveType type = toPrimitiveType(init.getType());
			final String name = init.getId();
			if (type == BoogieType.TYPE_ERROR) {
				addTypeError(name, new TypeErrorInfo(TypeErrorType.NONE_TYPE, init));
				continue;
			}

			if (init.getCategory() != VariableCategory.CONST) {
				addVar(name, type, init, mStateVars);
			} else {
				addVar(name, type, init, mConstVars);
			}
		}
	}

	private void extractVariablesFromAutomata(final Map<PatternType, PhaseEventAutomata> req2Automata) {
		for (final Entry<PatternType, PhaseEventAutomata> pattern2Aut : req2Automata.entrySet()) {
			final PatternType req = pattern2Aut.getKey();
			final PhaseEventAutomata currentAutomaton = pattern2Aut.getValue();

			addVar(getPcName(currentAutomaton), BoogieType.TYPE_INT, req, mPcVars);
			currentAutomaton.getClocks().forEach(a -> addVar(a, BoogieType.TYPE_REAL, req, mClockVars));

			for (final Entry<String, String> entry : currentAutomaton.getVariables().entrySet()) {
				final String name = entry.getKey();
				final String type = entry.getValue();

				if (type == null) {
					checkVar(name, req);
					continue;
				}

				switch (type.toLowerCase()) {
				case "bool":
				case "real":
				case "int":
					addVar(name, toPrimitiveType(type), req, mStateVars);
					break;
				case "event":
					addVar(name, BoogieType.TYPE_BOOL, req, mEventVars);
					break;
				default:
					addTypeError(name, new TypeErrorInfo(TypeErrorType.UNKNOWN_TYPE, req));
					break;
				}
			}
		}
	}

	private void checkVar(final String name, final PatternType source) {
		if (mId2Type.containsKey(name)) {
			return;
		}
		addTypeError(name, new TypeErrorInfo(TypeErrorType.MISSING_DECLARATION, source));
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
			addTypeError(name, new TypeErrorInfo(TypeErrorType.DUPLICATE_DECLARATION, source));
			mId2Type.put(name, BoogieType.TYPE_ERROR);
			return;
		}

		final ILocation loc = getLocation(source);
		final IdentifierExpression idExpr = ExpressionFactory.constructIdentifierExpression(loc, type, name,
				DeclarationInformation.DECLARATIONINFO_GLOBAL);
		mId2IdExpr.put(name, idExpr);
		mId2VarLHS.put(name, new VariableLHS(loc, name));
		if (!mPrimedVars.contains(name)) {
			addVar(getPrimedVarId(name), type, source, mPrimedVars);
		}
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

	private void addTypeError(final String name, final TypeErrorInfo typeErrorInfo) {
		final TypeErrorInfo oldTypeError = mId2TypeErrors.put(name, typeErrorInfo);
		if (oldTypeError != null) {
			mId2TypeErrors.put(name, oldTypeError.merge(typeErrorInfo));
			mLogger.error("Additional type error " + typeErrorInfo.mType + " for " + name);
		} else {
			mLogger.error("Type error " + typeErrorInfo.mType + " for " + name);
		}
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

	@Override
	public IdentifierExpression getIdentifierExpression(final String name) {
		final IdentifierExpression idExpr = mId2IdExpr.get(name);
		if (idExpr == null || idExpr.getType() == null) {
			throw new AssertionError();
		}
		assert idExpr != null && idExpr.getType() != null;
		return idExpr;
	}

	public Map<PatternType, BoogieLocation> getLocations() {
		return Collections.unmodifiableMap(mReq2Loc);
	}

	public List<Declaration> constructVariableDeclarations() {
		final List<Declaration> decls = new ArrayList<>();

		decls.add(constructVariableDeclaration(getDeltaVarName()));
		decls.addAll(constructVariableDeclarations(mClockVars));
		decls.addAll(constructVariableDeclarations(mPcVars));
		decls.addAll(constructVariableDeclarations(mConstVars));
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

	public static String getPrimedVarId(final String name) {
		return name + "'";
	}

	public String getDeltaVarName() {
		return mDeltaVar;
	}

	public static String getPcName(final PhaseEventAutomata aut) {
		return aut.getName() + "_pc";
	}

	public VariableLHS getVariableLhs(final String id) {
		return mId2VarLHS.get(id);
	}

	public Set<String> getStateVars() {
		return Collections.unmodifiableSet(mStateVars);
	}

	public Set<String> getPrimedVars() {
		return Collections.unmodifiableSet(mPrimedVars);
	}

	public Set<String> getEventVars() {
		return Collections.unmodifiableSet(mEventVars);
	}

	public Set<String> getClockVars() {
		return Collections.unmodifiableSet(mClockVars);
	}

	public Set<String> getPcVars() {
		return Collections.unmodifiableSet(mPcVars);
	}

	public Set<String> getConstVars() {
		return Collections.unmodifiableSet(mConstVars);
	}

	public Map<String, TypeErrorInfo> getTypeErrors() {
		return mId2TypeErrors;
	}

	public enum TypeErrorType {
		DUPLICATE_DECLARATION, UNKNOWN_TYPE, NO_DURATION_EXPRESSION, NO_DURATION_VALUE, NONE_TYPE, MISSING_DECLARATION
	}

	public static final class TypeErrorInfo {

		private final TypeErrorType mType;
		private final PatternType mSource;

		public TypeErrorInfo(final TypeErrorType type, final PatternType req) {
			mType = type;
			mSource = req;
		}

		public TypeErrorInfo merge(final TypeErrorInfo oldTypeError) {
			// TODO What should happen if we have more than one type error in one location?
			return this;
		}

		public PatternType getSource() {
			return mSource;
		}

		public TypeErrorType getType() {
			return mType;
		}

	}
}
