package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.standardfunctions;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CExpressionTranslator;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.DataRaceChecker;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryModelDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.ProcedureManager;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizeAndOffsetComputer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO.AUXVAR;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public class StringFunctionModelProvider extends FunctionModelProvider {
	public StringFunctionModelProvider(final Map<String, IASTNode> functionTable,
			final AuxVarInfoBuilder auxVarInfoBuilder, final INameHandler nameHandler,
			final ExpressionTranslation expressionTranslation, final MemoryHandler memoryHandler,
			final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer, final ProcedureManager procedureManager,
			final TypeSizes typeSizes, final TranslationSettings settings,
			final ExpressionResultTransformer expressionResultTransformer, final ITypeHandler typeHandler,
			final CExpressionTranslator cEpressionTranslator, final DataRaceChecker dataRaceChecker) {
		super(functionTable, auxVarInfoBuilder, nameHandler, expressionTranslation, memoryHandler,
				typeSizeAndOffsetComputer, procedureManager, typeSizes, settings, expressionResultTransformer,
				typeHandler, cEpressionTranslator, dataRaceChecker);
	}

	@Override
	public Collection<FunctionModel> getFunctionModels() {
		final List<FunctionModel> result = new ArrayList<>();

		result.add(new FunctionModel("__builtin_memcpy", this::handleMemcpy));
		result.add(new FunctionModel("__memcpy", this::handleMemcpy));
		result.add(new FunctionModel("memcpy", this::handleMemcpy));

		result.add(new FunctionModel("__builtin_memmove", this::handleMemmove));
		result.add(new FunctionModel("__memmove", this::handleMemmove));
		result.add(new FunctionModel("memmove", this::handleMemmove));
		result.add(new FunctionModel("memset", this::handleMemset));

		result.add(new FunctionModel("memcmp", this::handleMemCmp));

		result.add(new FunctionModel("__builtin_strchr", this::handleStrChr));
		result.add(new FunctionModel("strchr", this::handleStrChr));
		result.add(new FunctionModel("__builtin_strlen", this::handleStrLen));
		result.add(new FunctionModel("strlen", this::handleStrLen));
		result.add(new FunctionModel("__builtin_strcmp", this::handleStrCmp));
		result.add(new FunctionModel("strcmp", this::handleStrCmp));
		result.add(new FunctionModel("strncmp", this::handleStrnCmp));
		result.add(new FunctionModel("strcpy", this::handleStrCpy));
		result.add(new FunctionModel("strncpy", (main, node, loc, name) -> handleByOverapproximation(main, node, loc,
				name, 3, new CPointer(new CPrimitive(CPrimitives.CHAR)))));
		// https://en.cppreference.com/w/c/string/byte/toupper
		result.add(new FunctionModel("toupper", this::handleToUpper));

		// https://en.cppreference.com/w/c/string/byte/strtok
		result.add(new FunctionModel("strtok", (main, node, loc, name) -> handleByOverapproximation(main, node, loc,
				name, 2, new CPointer(new CPrimitive(CPrimitives.CHAR)))));

		// https://en.cppreference.com/w/c/string/byte/strcat
		result.add(new FunctionModel("strcat",
				(main, node, loc, name) -> handleUnsupportedFunctionByOverapproximation(main, loc, name,
						new CPointer(new CPrimitive(CPrimitives.CHAR)))));
		// https://en.cppreference.com/w/c/string/byte/strncat
		result.add(new FunctionModel("strncat",
				(main, node, loc, name) -> handleUnsupportedFunctionByOverapproximation(main, loc, name,
						new CPointer(new CPrimitive(CPrimitives.CHAR)))));

		// https://en.cppreference.com/w/c/string/byte/strcspn
		result.add(new FunctionModel("strcspn", (main, node, loc, name) -> handleByOverapproximation(main, node, loc,
				name, 2, new CPrimitive(CPrimitives.ULONG))));

		// https://en.cppreference.com/w/c/string/byte/strpbrk
		result.add(new FunctionModel("strpbrk", (main, node, loc, name) -> handleByOverapproximation(main, node, loc,
				name, 2, new CPointer(new CPrimitive(CPrimitives.CHAR)))));

		// https://en.cppreference.com/w/c/string/byte/memchr
		result.add(
				new FunctionModel("memchr", (main, node, loc, name) -> handleStringSearch(main, node, loc, name, 3)));
		// https://en.cppreference.com/w/c/string/byte/strstr
		result.add(
				new FunctionModel("strstr", (main, node, loc, name) -> handleStringSearch(main, node, loc, name, 2)));
		// https://en.cppreference.com/w/cpp/string/byte/strrchr
		result.add(
				new FunctionModel("strrchr", (main, node, loc, name) -> handleStringSearch(main, node, loc, name, 2)));

		// https://en.cppreference.com/w/c/string/byte/strerror
		result.add(new FunctionModel("strerror", this::handleStrerror));

		// https://en.cppreference.com/w/c/string/byte/strspn
		result.add(new FunctionModel("strspn", (main, node, loc, name) -> handleByOverapproximation(main, node, loc,
				name, 2, new CPrimitive(CPrimitives.ULONGLONG))));

		/**
		 * 7.22.1.3 The strtod, strtof, and strtold functions
		 *
		 * see https://en.cppreference.com/w/c/string/byte/strtof
		 *
		 * Interprets a floating-point value in a byte string pointed to by str. 2 arguments: pointer to the
		 * null-terminated byte string to be interpreted and pointer to a pointer to character.
		 *
		 * Floating-point value corresponding to the contents of str on success. If the converted value falls out of
		 * range of corresponding return type, range error occurs and HUGE_VAL, HUGE_VALF or HUGE_VALL is returned. If
		 * no conversion can be performed, ​0​ is returned.
		 *
		 * We handle this by overapproximation and do not check of range errors.
		 *
		 */
		result.add(new FunctionModel("strtof", (main, node, loc, name) -> handleByOverapproximation(main, node, loc,
				name, 2, new CPrimitive(CPrimitives.FLOAT))));
		result.add(new FunctionModel("strtod", (main, node, loc, name) -> handleByOverapproximation(main, node, loc,
				name, 2, new CPrimitive(CPrimitives.DOUBLE))));
		result.add(new FunctionModel("strtold", (main, node, loc, name) -> handleByOverapproximation(main, node, loc,
				name, 2, new CPrimitive(CPrimitives.LONGDOUBLE))));

		/**
		 * 7.22.1.4 The strtol, strtoll, strtoul, and strtoull functions
		 *
		 * see https://en.cppreference.com/w/c/string/byte/strtoul
		 *
		 * Interprets an unsigned integer value in a byte string pointed to by str.
		 *
		 * We handle this by overapproximation and do not check of range errors.
		 *
		 */
		result.add(new FunctionModel("strtol", (main, node, loc, name) -> handleByOverapproximation(main, node, loc,
				name, 3, new CPrimitive(CPrimitives.LONG))));
		result.add(new FunctionModel("strtoll", (main, node, loc, name) -> handleByOverapproximation(main, node, loc,
				name, 3, new CPrimitive(CPrimitives.LONGLONG))));
		result.add(new FunctionModel("strtoul", (main, node, loc, name) -> handleByOverapproximation(main, node, loc,
				name, 3, new CPrimitive(CPrimitives.ULONG))));
		result.add(new FunctionModel("strtoull", (main, node, loc, name) -> handleByOverapproximation(main, node, loc,
				name, 3, new CPrimitive(CPrimitives.ULONGLONG))));

		// https://en.cppreference.com/w/c/string/wide/iswxdigit
		result.add(new FunctionModel("iswxdigit", (main, node, loc, name) -> handleByOverapproximation(main, node, loc,
				name, 1, new CPrimitive(CPrimitives.INT))));

		return result;
	}

	@Override
	public Collection<String> getUnsupportedFunctions() {
		/**
		 * @formatter:off
		 * 7.22.7 Multibyte/wide character conversion functions
		 * 7.22.7.1 The mblen function
		 * 7.22.7.2 The mbtowc function
		 * 7.22.7.3 The wctomb function
		 *
		 * 7.22.8 Multibyte/wide string conversion functions
		 * 7.22.8.1 The mbstowcs function
		 * 7.22.8.2 The wcstombs function
		 * @formatter:on
		 */
		return List.of("mblen", "mbtowc", "wctomb", "mbstowcs", "wcstombs");
	}

	/**
	 * This function is used to model functions that perform string search and return a substring (like memchr, strstr,
	 * strrchr).
	 *
	 * We just dispatch the arguments and overapproximate the return value with some non-deterministic string.
	 */
	private Result handleStringSearch(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name, final int numberOfArguments) {
		final var builder = new ExpressionResultBuilder();
		checkArguments(loc, numberOfArguments, name, node.getArguments());
		for (final var arg : node.getArguments()) {
			if (!isStringLiteral(arg)) {
				final var argRes = (ExpressionResult) main.dispatch(arg);
				builder.addAllExceptLrValue(argRes);
			}
		}
		builder.addOverapprox(new Overapprox(name, loc));
		return builder.addAllIncludingLrValue(getNondetStringOrNull(loc)).build();
	}

	private Result handleStrerror(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		checkArguments(loc, 1, name, node.getArguments());
		// Just dispatch the argument and return a non-deterministic string
		return new ExpressionResultBuilder()
				.addAllExceptLrValue((ExpressionResult) main.dispatch(node.getArguments()[0]))
				.addAllIncludingLrValue(getNondetStringOrNull(loc)).build();
	}

	private ExpressionResult handleStrCmp(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 2, name, arguments);
		return handleMemoryComparison(main, loc, name, arguments[0], arguments[1]);
	}

	private ExpressionResult handleStrnCmp(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 3, name, arguments);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		builder.addAllExceptLrValue((ExpressionResult) main.dispatch(arguments[2]));
		builder.addAllIncludingLrValue(handleMemoryComparison(main, loc, name, arguments[0], arguments[1]));
		return builder.build();
	}

	/**
	 *
	 * char *strcpy( char *dest, const char *src );
	 *
	 * @param main
	 * @param node
	 * @param loc
	 * @param name
	 * @return
	 */
	private Result handleStrCpy(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {

		final MemoryModelDeclarations strCpyMmDecl = MemoryModelDeclarations.C_STRCPY;

		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 2, name, arguments);
		final CPointer charPointerType = new CPointer(new CPrimitive(CPrimitives.CHAR));
		final ExpressionResult dest = mExprResultTransformer.transformDispatchDecaySwitchImplicitConversion(main, loc,
				arguments[0], charPointerType);
		final ExpressionResult src = mExprResultTransformer.transformDispatchDecaySwitchImplicitConversion(main, loc,
				arguments[1], charPointerType);

		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
		resultBuilder.addAllExceptLrValue(dest);
		resultBuilder.addAllExceptLrValue(src);

		final AuxVarInfo auxvarinfo =
				mAuxVarInfoBuilder.constructAuxVarInfo(loc, dest.getLrValue().getCType(), SFO.AUXVAR.STRCPYRES);

		final CallStatement call = StatementFactory.constructCallStatement(loc, false,
				new VariableLHS[] { auxvarinfo.getLhs() }, strCpyMmDecl.getName(),
				new Expression[] { dest.getLrValue().getValue(), src.getLrValue().getValue() });
		for (final Overapprox oa : resultBuilder.getOverappr()) {
			oa.annotate(call);
		}
		resultBuilder.addAuxVarWithDeclaration(auxvarinfo);
		resultBuilder.addStatement(call);
		resultBuilder.setLrValue(new RValue(auxvarinfo.getExp(), CPointer.voidPointer()));

		// add marker for global declaration to memory handler
		mMemoryHandler.requireMemoryModelFeature(strCpyMmDecl);

		// add required information to function handler.
		mProcedureManager.registerProcedure(strCpyMmDecl.getName());
		// mProcedureManager.registerCall(mmDecl.getName());

		return resultBuilder.build();
	}

	private Result handleStrLen(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String methodName) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 1, methodName, arguments);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();

		final ExpressionResult arg =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		builder.addDeclarations(arg.getDeclarations());
		builder.addStatements(arg.getStatements());
		builder.addOverapprox(arg.getOverapprs());
		builder.addAuxVars(arg.getAuxVars());
		builder.addNeighbourUnionFields(arg.getNeighbourUnionFields());

		builder.addStatements(
				mMemoryHandler.constructMemsafetyChecksForPointerExpression(loc, arg.getLrValue().getValue()));

		// according to standard result is size_t, we use int for efficiency
		final CPrimitive resultType = new CPrimitive(CPrimitives.INT);
		// introduce fresh aux variable
		// final String tmpId = mNameHandler.getTempVarUID(SFO.AUXVAR.NONDET, resultType);
		// final VariableDeclaration tmpVarDecl =
		// SFO.getTempVarVariableDeclaration(tmpId, main.mTypeHandler.cType2AstType(loc, resultType), loc);
		final AuxVarInfo auxvarinfo = mAuxVarInfoBuilder.constructAuxVarInfo(loc, resultType, SFO.AUXVAR.NONDET);
		builder.addAuxVarWithDeclaration(auxvarinfo);

		// final IdentifierExpression tmpVarIdExpr = new IdentifierExpression(loc, tmpId);
		final Overapprox overAppFlag = new Overapprox(methodName, loc);
		builder.addOverapprox(overAppFlag);
		final RValue lrVal = new RValue(auxvarinfo.getExp(), resultType);
		builder.setLrValue(lrVal);
		return builder.build();
	}

	private Result handleStrChr(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		/*
		 * C11, 7.21.5.2 says: "#include <string.h> char *strchr(const char *s, int c);
		 *
		 * Description: The strchr function locates the first occurrence of c (converted to a char) in the string
		 * pointed to by s. The terminating null character is considered to be part of the string. Returns : The strchr
		 * function returns a pointer to the located character, or a null pointer if the character does not occur in the
		 * string."
		 *
		 * We replace the method call by a fresh char pointer variable which is havocced, and assumed to be either NULL
		 * or a pointer into the area where the argument pointer is valid.
		 */
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 2, name, arguments);
		// dispatch first argument -- we need its value for the assume

		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final ExpressionResult argS =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		builder.addDeclarations(argS.getDeclarations()).addStatements(argS.getStatements())
				.addOverapprox(argS.getOverapprs()).addAuxVars(argS.getAuxVars())
				.addNeighbourUnionFields(argS.getNeighbourUnionFields());

		// dispatch second argument -- only for its sideeffects
		final ExpressionResult argC =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[1]);
		builder.addDeclarations(argC.getDeclarations()).addStatements(argC.getStatements())
				.addOverapprox(argC.getOverapprs()).addAuxVars(argC.getAuxVars())
				.addNeighbourUnionFields(argC.getNeighbourUnionFields());

		// introduce fresh aux variable
		final CPointer resultType = new CPointer(new CPrimitive(CPrimitives.CHAR));
		final AuxVarInfo auxvarinfo = mAuxVarInfoBuilder.constructAuxVarInfo(loc, resultType, SFO.AUXVAR.NONDET);
		builder.addAuxVarWithDeclaration(auxvarinfo);

		final Expression nullExpr = mExpressionTranslation.constructNullPointer(loc);

		/*
		 * if we are in memsafety-mode: add assertions that check that arg_s.lrVal.getValue is a valid pointer
		 *
		 * technical Notes: these assertions are added before the assume statement and before the result can be assigned
		 * thus the overapproximation introduced does not affect violations of these assertions
		 */
		builder.addStatements(
				mMemoryHandler.constructMemsafetyChecksForPointerExpression(loc, argS.getLrValue().getValue()));

		// the havocced/uninitialized variable that represents the return value
		final Expression tmpExpr = auxvarinfo.getExp();// new IdentifierExpression(loc, tmpId);

		/*
		 * build the assume statement as described above
		 */
		{
			// res.base == 0 && res.offset == 0
			final Expression baseEqualsNull = mExpressionTranslation.constructBinaryComparisonIntegerExpression(loc,
					IASTBinaryExpression.op_equals, MemoryHandler.getPointerBaseAddress(tmpExpr, loc),
					mExpressionTranslation.getCTypeOfPointerComponents(),
					MemoryHandler.getPointerBaseAddress(nullExpr, loc),
					mExpressionTranslation.getCTypeOfPointerComponents());
			final Expression offsetEqualsNull = mExpressionTranslation.constructBinaryComparisonIntegerExpression(loc,
					IASTBinaryExpression.op_equals, MemoryHandler.getPointerOffset(tmpExpr, loc),
					mExpressionTranslation.getCTypeOfPointerComponents(), MemoryHandler.getPointerOffset(nullExpr, loc),
					mExpressionTranslation.getCTypeOfPointerComponents());
			final Expression equalsNull =
					ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND, baseEqualsNull, offsetEqualsNull);
			// old solution did not work quickly..
			// final BinaryExpression equalsNull = expressionTranslation.constructBinaryComparisonExpression(loc,
			// new BinaryExpression(loc, Operator.COMPEQ, tmpExpr, nullExpr);
			// res.base == arg_s.base
			final Expression baseEquals = mExpressionTranslation.constructBinaryComparisonIntegerExpression(loc,
					IASTBinaryExpression.op_equals, MemoryHandler.getPointerBaseAddress(tmpExpr, loc),
					mExpressionTranslation.getCTypeOfPointerComponents(),
					MemoryHandler.getPointerBaseAddress(argS.getLrValue().getValue(), loc),
					mExpressionTranslation.getCTypeOfPointerComponents());
			// res.offset >= 0
			final Expression offsetNonNegative = mExpressionTranslation.constructBinaryComparisonIntegerExpression(loc,
					IASTBinaryExpression.op_lessEqual,
					mTypeSizes.constructLiteralForIntegerType(loc, mExpressionTranslation.getCTypeOfPointerComponents(),
							new BigInteger("0")),
					mExpressionTranslation.getCTypeOfPointerComponents(), MemoryHandler.getPointerOffset(tmpExpr, loc),
					mExpressionTranslation.getCTypeOfPointerComponents());
			// res.offset < length(arg_s.base)
			final Expression offsetSmallerLength = mExpressionTranslation.constructBinaryComparisonIntegerExpression(
					loc, IASTBinaryExpression.op_lessEqual, MemoryHandler.getPointerOffset(tmpExpr, loc),
					mExpressionTranslation.getCTypeOfPointerComponents(),
					ExpressionFactory.constructNestedArrayAccessExpression(loc, mMemoryHandler.getLengthArray(loc),
							new Expression[] {
									MemoryHandler.getPointerBaseAddress(argS.getLrValue().getValue(), loc) }),
					mExpressionTranslation.getCTypeOfPointerComponents());
			// res.base == arg_s.base && res.offset >= 0 && res.offset <= length(arg_s.base)
			final Expression inRange =
					ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND, baseEquals, ExpressionFactory
							.newBinaryExpression(loc, Operator.LOGICAND, offsetNonNegative, offsetSmallerLength));
			// assume equalsNull or inRange
			final AssumeStatement assume = new AssumeStatement(loc,
					ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, equalsNull, inRange));
			builder.addStatement(assume);
		}

		// final List<Overapprox> overapprox = new ArrayList<>();
		final Overapprox overappFlag = new Overapprox(name, loc);
		// overapprox.add(overappFlag);
		// assume.getPayload().getAnnotations().put(Overapprox.getIdentifier(), overappFlag);
		builder.addOverapprox(overappFlag);

		final RValue lrVal = new RValue(tmpExpr, resultType);
		builder.setLrValue(lrVal);

		return builder.build();
	}

	private Result handleToUpper(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		// Translate toupper(x) to x >= 'a' && x <= 'z' ? x - 32 : x
		// (with 'a' = 97 and 'z' = 122)
		// This function might translate more lower-case chars (depending on the C locale), but we ignore that for now.
		checkArguments(loc, 1, name, node.getArguments());
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final ExpressionResult argRes =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, node.getArguments()[0]);
		builder.addAllExceptLrValue(argRes);
		final Expression arg = argRes.getLrValue().getValue();
		final CPrimitive type = new CPrimitive(CPrimitives.INT);
		final Expression a = mExpressionTranslation.constructLiteralForIntegerType(loc, type, BigInteger.valueOf(97));
		final Expression z = mExpressionTranslation.constructLiteralForIntegerType(loc, type, BigInteger.valueOf(122));
		final Expression greaterA = mExpressionTranslation.constructBinaryComparisonExpression(loc,
				IASTBinaryExpression.op_greaterEqual, arg, type, a, type);
		final Expression smallerZ = mExpressionTranslation.constructBinaryComparisonExpression(loc,
				IASTBinaryExpression.op_lessEqual, arg, type, z, type);
		final Expression isLower = ExpressionFactory.and(loc, List.of(greaterA, smallerZ));
		final Expression upperArg =
				mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_minus, arg, type,
						mExpressionTranslation.constructLiteralForIntegerType(loc, type, BigInteger.valueOf(32)), type);
		final Expression ite = ExpressionFactory.constructIfThenElseExpression(loc, isLower, upperArg, arg);
		return builder.setLrValue(new RValue(ite, type)).build();
	}

	private ExpressionResult handleMemCmp(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 3, name, arguments);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		builder.addAllExceptLrValue((ExpressionResult) main.dispatch(arguments[2]));
		builder.addAllIncludingLrValue(handleMemoryComparison(main, loc, name, arguments[0], arguments[1]));
		return builder.build();
	}

	private ExpressionResult handleMemoryComparison(final IDispatcher main, final ILocation loc, final String name,
			final IASTInitializerClause mem1, final IASTInitializerClause mem2) {
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final ExpressionResult arg0 = mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, mem1);
		builder.addDeclarations(arg0.getDeclarations());
		builder.addStatements(arg0.getStatements());
		builder.addOverapprox(arg0.getOverapprs());
		builder.addAuxVars(arg0.getAuxVars());
		builder.addNeighbourUnionFields(arg0.getNeighbourUnionFields());

		builder.addStatements(
				mMemoryHandler.constructMemsafetyChecksForPointerExpression(loc, arg0.getLrValue().getValue()));

		final ExpressionResult arg1 = mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, mem2);
		builder.addDeclarations(arg1.getDeclarations());
		builder.addStatements(arg1.getStatements());
		builder.addOverapprox(arg1.getOverapprs());
		builder.addAuxVars(arg1.getAuxVars());
		builder.addNeighbourUnionFields(arg1.getNeighbourUnionFields());

		builder.addStatements(
				mMemoryHandler.constructMemsafetyChecksForPointerExpression(loc, arg1.getLrValue().getValue()));

		final CPrimitive resultType = new CPrimitive(CPrimitives.INT);
		// introduce fresh aux variable
		// final String tmpId = mNameHandler.getTempVarUID(SFO.AUXVAR.NONDET, resultType);
		// final VariableDeclaration tmpVarDecl =
		// SFO.getTempVarVariableDeclaration(tmpId, main.mTypeHandler.cType2AstType(loc, resultType), loc);
		final AuxVarInfo auxvarinfo = mAuxVarInfoBuilder.constructAuxVarInfo(loc, resultType, SFO.AUXVAR.NONDET);
		builder.addAuxVarWithDeclaration(auxvarinfo);

		final Overapprox overAppFlag = new Overapprox(name, loc);
		builder.addOverapprox(overAppFlag);
		final RValue lrVal = new RValue(auxvarinfo.getExp(), resultType);
		builder.setLrValue(lrVal);
		return builder.build();
	}

	private Result handleMemset(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		/*
		 * C11 says in 7.24.6.1 void *memset(void *s, int c, size_t n); The memset function copies the value of c
		 * (converted to an unsigned char) into each of the first n characters of the object pointed to by s.
		 */
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 3, name, arguments);

		final ExpressionResult dispatchedArgS =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		final ExpressionResult dispatchedArgC =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[1]);
		final ExpressionResult dispatchedArgN =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[2]);

		// TODO: No conversion for ArgS?
		final ExpressionResult convertedArgC =
				mExpressionTranslation.convertIntToInt(loc, dispatchedArgC, new CPrimitive(CPrimitives.INT));
		final ExpressionResult convertedArgN =
				mExpressionTranslation.convertIntToInt(loc, dispatchedArgN, mTypeSizeComputer.getSizeT());

		final ExpressionResultBuilder result = new ExpressionResultBuilder().setLrValue(dispatchedArgS.getLrValue());

		result.addAllExceptLrValue(dispatchedArgS);
		result.addAllExceptLrValue(convertedArgC);
		result.addAllExceptLrValue(convertedArgN);

		final CPointer voidPointerType = CPointer.voidPointer();
		final AuxVarInfo auxvar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, voidPointerType, SFO.AUXVAR.MEMSETRES);
		result.addAuxVarWithDeclaration(auxvar);

		result.addStatement(mMemoryHandler.constructUltimateMemsetCall(loc, dispatchedArgS.getLrValue().getValue(),
				convertedArgC.getLrValue().getValue(), convertedArgN.getLrValue().getValue(), auxvar.getLhs()));
		return result.build();
	}

	private Result handleMemcpy(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		return handleMemCopyOrMove(main, node, loc, name, SFO.AUXVAR.MEMCPYRES, MemoryModelDeclarations.C_MEMCPY);
	}

	private Result handleMemmove(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		return handleMemCopyOrMove(main, node, loc, name, SFO.AUXVAR.MEMMOVERES, MemoryModelDeclarations.C_MEMMOVE);
	}

	private Result handleMemCopyOrMove(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name, final AUXVAR auxVar, final MemoryModelDeclarations mmDecl) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 3, name, arguments);
		final CPointer voidType = CPointer.voidPointer();
		final ExpressionResult dest = mExprResultTransformer.transformDispatchDecaySwitchImplicitConversion(main, loc,
				arguments[0], voidType);
		final ExpressionResult src = mExprResultTransformer.transformDispatchDecaySwitchImplicitConversion(main, loc,
				arguments[1], voidType);
		final ExpressionResult size = mExprResultTransformer.transformDispatchDecaySwitchImplicitConversion(main, loc,
				arguments[2], mTypeSizeComputer.getSizeT());

		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
		resultBuilder.addAllExceptLrValue(dest);
		resultBuilder.addAllExceptLrValue(src);
		resultBuilder.addAllExceptLrValue(size);

		final AuxVarInfo auxvarinfo = mAuxVarInfoBuilder.constructAuxVarInfo(loc, dest.getLrValue().getCType(), auxVar);

		final CallStatement call = StatementFactory.constructCallStatement(loc, false,
				new VariableLHS[] { auxvarinfo.getLhs() }, mmDecl.getName(), new Expression[] {
						dest.getLrValue().getValue(), src.getLrValue().getValue(), size.getLrValue().getValue() });
		resultBuilder.addAuxVarWithDeclaration(auxvarinfo);
		resultBuilder.addStatement(call);
		resultBuilder.setLrValue(new RValue(auxvarinfo.getExp(), CPointer.voidPointer()));

		// add marker for global declaration to memory handler
		mMemoryHandler.requireMemoryModelFeature(mmDecl);

		// add required information to function handler.
		mProcedureManager.registerProcedure(mmDecl.getName());
		// mProcedureManager.registerCall(mmDecl.getName());

		return resultBuilder.build();
	}
}
