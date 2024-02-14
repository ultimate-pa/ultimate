/*
 * Copyright (C) 2013-2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.standardfunctions;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTLiteralExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTIdExpression;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTUnaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.JoinStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WildcardExpression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CExpressionTranslator;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationResultReporter;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.DataRaceChecker;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.LocalLValueILocationPair;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler.MemoryArea;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryModelDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.ProcedureManager;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizeAndOffsetComputer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.FloatFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.FloatSupportInUltimate;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValueFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.SkipResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO.AUXVAR;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.CheckMessageProvider;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Spec;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * The {@link StandardFunctionHandler} creates the translation for various functions where we have our own specification
 * or implementation. This is typically the case for functions defined in the C standard, but also for various standard
 * libraries or SV-COMP extensions.
 *
 * @author Markus Lindenmann,
 * @author Matthias Heizmann
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class StandardFunctionHandler {

	/**
	 * If we construct an auxvar that models a nondeterministic input, we havoc that auxvar afterwards to ensure that we
	 * get a new nondeterministic value even if the variable occurs in a loop. If this constant is set, we havoc the
	 * variable also before the nondeterministic assignment. If the auxvar is also havoced before, it is only
	 * backward-live to the havoc, otherwise it would be backward-live until the beginning of the procedure.
	 */
	private static final boolean HAVOC_NONDET_AUXVARS_ALSO_BEFORE = true;

	/**
	 * See MEMORY_ORDER_SEQ_CST in stdatomic.h
	 */
	private static final int MEMORY_ORDER_SEQ_CST = 5;

	private final LocationFactory mLocationFactory;

	private final Map<String, IFunctionModelHandler> mFunctionModels;

	private final ExpressionTranslation mExpressionTranslation;

	private final MemoryHandler mMemoryHandler;

	private final TypeSizeAndOffsetComputer mTypeSizeComputer;

	private final ProcedureManager mProcedureManager;

	private final CTranslationResultReporter mReporter;

	private final Map<String, IASTNode> mFunctionTable;

	private final AuxVarInfoBuilder mAuxVarInfoBuilder;

	private final INameHandler mNameHandler;

	private final TypeSizes mTypeSizes;

	private final FlatSymbolTable mSymboltable;

	private final TranslationSettings mSettings;

	private final ExpressionResultTransformer mExprResultTransformer;

	private final ITypeHandler mTypeHandler;

	private final CExpressionTranslator mCEpressionTranslator;

	private final ThreadIdManager mThreadIdManager;

	private final DataRaceChecker mDataRaceChecker;

	private final ILogger mLogger;

	public StandardFunctionHandler(final ILogger logger, final Map<String, IASTNode> functionTable,
			final AuxVarInfoBuilder auxVarInfoBuilder, final INameHandler nameHandler,
			final ExpressionTranslation expressionTranslation, final MemoryHandler memoryHandler,
			final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer, final ProcedureManager procedureManager,
			final CTranslationResultReporter reporter, final TypeSizes typeSizes, final FlatSymbolTable symboltable,
			final TranslationSettings settings, final ExpressionResultTransformer expressionResultTransformer,
			final LocationFactory locationFactory, final ITypeHandler typeHandler,
			final CExpressionTranslator cEpressionTranslator, final DataRaceChecker dataRaceChecker) {
		mLogger = logger;
		mExpressionTranslation = expressionTranslation;
		mMemoryHandler = memoryHandler;
		mTypeSizeComputer = typeSizeAndOffsetComputer;
		mProcedureManager = procedureManager;
		mReporter = reporter;
		mFunctionTable = functionTable;
		mAuxVarInfoBuilder = auxVarInfoBuilder;
		mNameHandler = nameHandler;
		mTypeSizes = typeSizes;
		mSymboltable = symboltable;
		mSettings = settings;
		mExprResultTransformer = expressionResultTransformer;
		mLocationFactory = locationFactory;
		mTypeHandler = typeHandler;
		mCEpressionTranslator = cEpressionTranslator;
		mFunctionModels = getFunctionModels();
		mThreadIdManager = new ThreadIdManager(mAuxVarInfoBuilder, mExprResultTransformer, mExpressionTranslation,
				mMemoryHandler, mTypeHandler, mTypeSizes, null /* TODO */, symboltable);
		mDataRaceChecker = dataRaceChecker;
	}

	/**
	 * Check if the given function has an "integrated" specification or implementation and return a {@link Result} that
	 * contains a translation of the function if this is the case.
	 *
	 * Return null otherwise.
	 *
	 * @param main
	 * @param node
	 * @param astIdExpression
	 * @return
	 */
	public Result translateStandardFunction(final IDispatcher main, final IASTFunctionCallExpression node,
			final IASTIdExpression astIdExpression) {
		assert node
				.getFunctionNameExpression() == astIdExpression : "astIdExpression is not the name of the called function";
		final String name = astIdExpression.getName().toString();

		final IFunctionModelHandler functionModel = mFunctionModels.get(name);
		if (functionModel != null) {
			final String transformedName = mSymboltable.applyMultiparseRenaming(node.getContainingFilename(), name);
			final IASTNode funDecl = mFunctionTable.get(transformedName);
			if (funDecl instanceof IASTFunctionDefinition) {
				// it is a function that already has a body
				if (!mSettings.checkErrorFunction() || !"reach_error".equals(transformedName)) {
					return null;
				}
				mLogger.warn(String.format(
						"Function %s is already implemented but we override the implementation for the call at %s",
						transformedName, node.getFileLocation()));
			}
			final ILocation loc = mLocationFactory.createCLocation(node);
			return functionModel.handleFunction(main, node, loc, name);
		}
		return null;
	}

	private Map<String, IFunctionModelHandler> getFunctionModels() {
		final Map<String, IFunctionModelHandler> map = new HashMap<>();

		// Do not use skip for functions that have return values, use constructUnsoundOverapproximationForFunctionCall
		// instead
		final IFunctionModelHandler skip = (main, node, loc, name) -> handleByIgnore(main, loc, name);
		final IFunctionModelHandler die = (main, node, loc, name) -> handleByUnsupportedSyntaxException(loc, name);
		final IFunctionModelHandler dieFloat =
				(main, node, loc, name) -> handleByUnsupportedSyntaxExceptionKnown(loc, "math.h", name);

		for (final String unsupportedFloatFunction : FloatSupportInUltimate.getUnsupportedFloatOperations()) {
			fill(map, unsupportedFloatFunction, dieFloat);
		}
		for (final var overapprox : FloatSupportInUltimate.getOverapproximatedUnaryFunctions().entrySet()) {
			fill(map, overapprox.getKey(), (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name,
					1, new CPrimitive(overapprox.getValue())));
		}

		/** functions of pthread library **/
		fill(map, "pthread_create", this::handlePthread_create);
		fill(map, "pthread_join", this::handlePthread_join);
		fill(map, "pthread_mutex_init", this::handlePthread_mutex_init);
		fill(map, "pthread_mutex_lock", this::handlePthread_mutex_lock);
		fill(map, "pthread_mutex_trylock", this::handlePthread_mutex_trylock);
		fill(map, "pthread_mutex_unlock", this::handlePthread_mutex_unlock);
		fill(map, "pthread_exit", this::handlePthread_exit);
		fill(map, "pthread_cond_init", this::handlePthread_success);
		fill(map, "pthread_cond_wait", this::handlePthread_cond_wait);
		fill(map, "pthread_cond_signal", this::handlePthread_success);
		fill(map, "pthread_cond_broadcast", this::handlePthread_success);
		fill(map, "pthread_cond_destroy", this::handlePthread_success);
		fill(map, "pthread_mutex_destroy", this::handlePthread_success);
		fill(map, "pthread_rwlock_rdlock", this::handlePthread_rwlock_rdlock);
		fill(map, "pthread_rwlock_wrlock", this::handlePthread_rwlock_wrlock);
		fill(map, "pthread_rwlock_unlock", this::handlePthread_rwlock_unlock);
		// the following three occur at SV-COMP 2019 only in one benchmark
		fill(map, "pthread_attr_init", die);
		fill(map, "pthread_attr_setdetachstate", die);
		fill(map, "pthread_attr_destroy", die);
		// the following three occur at SV-COMP 2019 only in some pthread-divine benchmarks
		fill(map, "pthread_key_create", die);
		fill(map, "pthread_getspecific", die);
		fill(map, "pthread_setspecific", die);
		// further unsupported pthread functions
		fill(map, "pthread_rwlock_init", die);

		/** Semaphores https://pubs.opengroup.org/onlinepubs/7908799/xsh/semaphore.h.html **/
		fill(map, "sem_close", die);
		fill(map, "sem_destroy", die);
		fill(map, "sem_getvalue", die);
		fill(map, "sem_init", die);
		fill(map, "sem_open", die);
		fill(map, "sem_post", die);
		fill(map, "sem_trywait", die);
		fill(map, "sem_unlink", die);
		fill(map, "sem_wait", die);

		fill(map, "printf", (main, node, loc, name) -> handlePrintF(main, node, loc));

		// https://en.cppreference.com/w/c/io/fgets
		fill(map, "fgets", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 2,
				new CPointer(new CPrimitive(CPrimitives.CHAR))));

		// https://en.cppreference.com/w/c/io/fgetc
		fill(map, "fgetc", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 1,
				new CPrimitive(CPrimitives.INT)));

		// TODO 20211105 Matthias: Unsound because our implementation of printf is
		// unsound and because we consider wchars as chars.
		fill(map, "wprintf", (main, node, loc, name) -> handlePrintF(main, node, loc));
		fill(map, "fprintf", (main, node, loc, name) -> handlePrintFunction(main, node, loc));
		fill(map, "sprintf", (main, node, loc, name) -> handleSPrintF(main, node, loc));
		fill(map, "snprintf", (main, node, loc, name) -> handleSnPrintF(main, node, loc));

		// https://en.cppreference.com/w/c/io/fscanf
		fill(map, "scanf", (main, node, loc, name) -> handleScanf(name, main, node, loc, 1));
		fill(map, "scanf_s", (main, node, loc, name) -> handleScanf(name, main, node, loc, 1));
		fill(map, "fscanf", (main, node, loc, name) -> handleScanf(name, main, node, loc, 2));
		fill(map, "fscanf_s", (main, node, loc, name) -> handleScanf(name, main, node, loc, 2));
		fill(map, "sscanf", (main, node, loc, name) -> handleScanf(name, main, node, loc, 2));
		fill(map, "sscanf_s", (main, node, loc, name) -> handleScanf(name, main, node, loc, 2));

		// https://en.cppreference.com/w/c/io/fwscanf
		fill(map, "wscanf", (main, node, loc, name) -> handleScanf(name, main, node, loc, 1));
		fill(map, "wscanf_s", (main, node, loc, name) -> handleScanf(name, main, node, loc, 1));
		fill(map, "fwscanf", (main, node, loc, name) -> handleScanf(name, main, node, loc, 2));
		fill(map, "fwscanf_s", (main, node, loc, name) -> handleScanf(name, main, node, loc, 2));
		fill(map, "swscanf", (main, node, loc, name) -> handleScanf(name, main, node, loc, 2));
		fill(map, "swscanf_s", (main, node, loc, name) -> handleScanf(name, main, node, loc, 2));

		// https://en.cppreference.com/w/c/io/puts
		fill(map, "puts", this::handlePuts);

		fill(map, "__builtin_memcpy", this::handleMemcpy);
		fill(map, "__memcpy", this::handleMemcpy);
		fill(map, "memcpy", this::handleMemcpy);

		fill(map, "__builtin_memmove", this::handleMemmove);
		fill(map, "__memmove", this::handleMemmove);
		fill(map, "memmove", this::handleMemmove);

		fill(map, "memcmp", this::handleMemCmp);

		fill(map, "alloca", this::handleAlloc);
		fill(map, "__builtin_alloca", this::handleAlloc);
		fill(map, "memset", this::handleMemset);

		/*
		 * See https://gcc.gnu.org/onlinedocs/gcc/Other-Builtins.html
		 */
		fill(map, "__builtin_popcount", die);
		fill(map, "__builtin_popcountl", die);
		fill(map, "__builtin_popcountll", die);

		/*
		 * The GNU C online documentation at https://gcc.gnu.org/onlinedocs/gcc/Return-Address.html on 09 Nov 2016 says:
		 * "— Built-in Function: void * __builtin_return_address (unsigned int level) This function returns the return
		 * address of the current function, or of one of its callers. The level argument is number of frames to scan up
		 * the call stack. A value of 0 yields the return address of the current function, a value of 1 yields the
		 * return address of the caller of the current function, and so forth. When inlining the expected behavior is
		 * that the function returns the address of the function that is returned to. To work around this behavior use
		 * the noinline function attribute.
		 *
		 * The level argument must be a constant integer. On some machines it may be impossible to determine the return
		 * address of any function other than the current one; in such cases, or when the top of the stack has been
		 * reached, this function returns 0 or a random value. In addition, __builtin_frame_address may be used to
		 * determine if the top of the stack has been reached. Additional post-processing of the returned value may be
		 * needed, see __builtin_extract_return_addr. Calling this function with a nonzero argument can have
		 * unpredictable effects, including crashing the calling program. As a result, calls that are considered unsafe
		 * are diagnosed when the -Wframe-address option is in effect. Such calls should only be made in debugging
		 * situations."
		 *
		 * Current solution: replace call by a havoced aux variable.
		 */
		fill(map, "__builtin_return_address", (main, node, loc, name) -> handleByOverapproximation(main, node, loc,
				name, 1, new CPointer(new CPrimitive(CPrimitives.VOID))));

		fill(map, "__builtin_bswap16", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 1,
				new CPrimitive(CPrimitives.USHORT)));
		fill(map, "__builtin_bswap32", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 1,
				new CPrimitive(CPrimitives.UINT)));
		fill(map, "__builtin_bswap64", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 1,
				new CPrimitive(CPrimitives.ULONG)));

		/*
		 * 6.56 Built-in Functions to Perform Arithmetic with Overflow Checking
		 * https://gcc.gnu.org/onlinedocs/gcc/Integer-Overflow-Builtins.html
		 */
		final IFunctionModelHandler overapproximateGccOverflowCheck = (main, node, loc,
				name) -> handleByOverapproximation(main, node, loc, name, 3, new CPrimitive(CPrimitives.BOOL));
		fill(map, "__builtin_add_overflow", overapproximateGccOverflowCheck);
		fill(map, "__builtin_sadd_overflow", overapproximateGccOverflowCheck);
		fill(map, "__builtin_saddl_overflow", overapproximateGccOverflowCheck);
		fill(map, "__builtin_saddll_overflow", overapproximateGccOverflowCheck);
		fill(map, "__builtin_uadd_overflow", overapproximateGccOverflowCheck);
		fill(map, "__builtin_uaddl_overflow", overapproximateGccOverflowCheck);
		fill(map, "__builtin_uaddll_overflow", overapproximateGccOverflowCheck);
		fill(map, "__builtin_sub_overflow", overapproximateGccOverflowCheck);
		fill(map, "__builtin_ssub_overflow", overapproximateGccOverflowCheck);
		fill(map, "__builtin_ssubl_overflow", overapproximateGccOverflowCheck);
		fill(map, "__builtin_ssubll_overflow", overapproximateGccOverflowCheck);
		fill(map, "__builtin_usub_overflow", overapproximateGccOverflowCheck);
		fill(map, "__builtin_usubl_overflow", overapproximateGccOverflowCheck);
		fill(map, "__builtin_usubll_overflow", overapproximateGccOverflowCheck);
		fill(map, "__builtin_mul_overflow", overapproximateGccOverflowCheck);
		fill(map, "__builtin_smul_overflow", overapproximateGccOverflowCheck);
		fill(map, "__builtin_smull_overflow", overapproximateGccOverflowCheck);
		fill(map, "__builtin_smulll_overflow", overapproximateGccOverflowCheck);
		fill(map, "__builtin_umul_overflow", overapproximateGccOverflowCheck);
		fill(map, "__builtin_umull_overflow", overapproximateGccOverflowCheck);
		fill(map, "__builtin_umulll_overflow", overapproximateGccOverflowCheck);
		fill(map, "__builtin_add_overflow_p", overapproximateGccOverflowCheck);
		fill(map, "__builtin_sub_overflow_p", overapproximateGccOverflowCheck);
		fill(map, "__builtin_mul_overflow_p", overapproximateGccOverflowCheck);

		// Atomic operations https://en.cppreference.com/w/c/atomic
		// Preprocessing leads to: https://gcc.gnu.org/onlinedocs/gcc/_005f_005fatomic-Builtins.html

		fill(map, "__atomic_load", this::handleAtomicLoad);
		fill(map, "__atomic_exchange", this::handleAtomicExchange);
		fill(map, "__atomic_store", this::handleAtomicStore);

		fill(map, "__atomic_load_n", this::handleAtomicLoadN);
		fill(map, "__atomic_store_n", this::handleAtomicStoreN);
		fill(map, "__atomic_exchange_n", this::handleAtomicExchangeN);

		fill(map, "__atomic_fetch_add",
				(main, node, loc, name) -> handleAtomicFetch(main, node, loc, name, IASTBinaryExpression.op_plus));
		fill(map, "__atomic_fetch_sub",
				(main, node, loc, name) -> handleAtomicFetch(main, node, loc, name, IASTBinaryExpression.op_minus));
		fill(map, "__atomic_fetch_and",
				(main, node, loc, name) -> handleAtomicFetch(main, node, loc, name, IASTBinaryExpression.op_binaryAnd));
		fill(map, "__atomic_fetch_or",
				(main, node, loc, name) -> handleAtomicFetch(main, node, loc, name, IASTBinaryExpression.op_binaryOr));
		fill(map, "__atomic_fetch_xor",
				(main, node, loc, name) -> handleAtomicFetch(main, node, loc, name, IASTBinaryExpression.op_binaryXor));

		fill(map, "__atomic_test_and_set", this::handleAtomicTestAndSet);
		fill(map, "__atomic_clear", this::handleAtomicClear);

		fill(map, "__atomic_compare_exchange",
				(main, node, loc, name) -> handleUnsupportedFunctionByOverapproximation(main, loc, name,
						new CPrimitive(CPrimitives.BOOL)));
		fill(map, "__atomic_compare_exchange_n",
				(main, node, loc, name) -> handleUnsupportedFunctionByOverapproximation(main, loc, name,
						new CPrimitive(CPrimitives.BOOL)));
		fill(map, "__atomic_thread_fence", (main, node, loc, name) -> handleUnsupportedFunctionByOverapproximation(main,
				loc, name, new CPrimitive(CPrimitives.VOID)));
		fill(map, "__atomic_signal_fence", (main, node, loc, name) -> handleUnsupportedFunctionByOverapproximation(main,
				loc, name, new CPrimitive(CPrimitives.VOID)));
		fill(map, "__atomic_always_lock_free", (main, node, loc, name) -> handleByOverapproximation(main, node, loc,
				name, 2, new CPrimitive(CPrimitives.BOOL)));
		fill(map, "__atomic_is_lock_free", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name,
				2, new CPrimitive(CPrimitives.BOOL)));

		/*
		 * builtin_prefetch according to https://gcc.gnu.org/onlinedocs/gcc-3.4.5/gcc/Other-Builtins.html (state:
		 * 5.6.2015) triggers the processor to load something into cache, does nothing else is void thus has no return
		 * value
		 */
		fill(map, "__builtin_prefetch", skip);

		fill(map, "__builtin_expect", this::handleBuiltinExpect);
		fill(map, "__builtin_unreachable", (main, node, loc, name) -> handleBuiltinUnreachable(loc));
		fill(map, "__builtin_object_size", this::handleBuiltinObjectSize);

		/** various string builtins **/
		fill(map, "__builtin_strchr", this::handleStrChr);
		fill(map, "strchr", this::handleStrChr);
		fill(map, "__builtin_strlen", this::handleStrLen);
		fill(map, "strlen", this::handleStrLen);
		fill(map, "__builtin_strcmp", this::handleStrCmp);
		fill(map, "strcmp", this::handleStrCmp);
		fill(map, "strncmp", this::handleStrnCmp);
		fill(map, "strcpy", this::handleStrCpy);
		fill(map, "strncpy", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 3,
				new CPointer(new CPrimitive(CPrimitives.CHAR))));

		/** various float builtins **/
		fill(map, "nan", (main, node, loc, name) -> handleNaNOrInfinity(loc, name));
		fill(map, "nanf", (main, node, loc, name) -> handleNaNOrInfinity(loc, name));
		fill(map, "nanl", (main, node, loc, name) -> handleNaNOrInfinity(loc, name));
		fill(map, "__builtin_nan", (main, node, loc, name) -> handleNaNOrInfinity(loc, "nan"));
		fill(map, "__builtin_nanf", (main, node, loc, name) -> handleNaNOrInfinity(loc, "nanf"));
		fill(map, "__builtin_nanl", (main, node, loc, name) -> handleNaNOrInfinity(loc, "nanl"));
		fill(map, "__builtin_inff", (main, node, loc, name) -> handleNaNOrInfinity(loc, "inff"));
		fill(map, "__builtin_huge_val", (main, node, loc, name) -> handleNaNOrInfinity(loc, "inf"));
		fill(map, "__builtin_huge_valf", (main, node, loc, name) -> handleNaNOrInfinity(loc, "inff"));
		fill(map, "__builtin_isgreater", (main, node, loc, name) -> handleFloatBuiltinBinaryComparison(main, node, loc,
				name, IASTBinaryExpression.op_greaterThan));
		fill(map, "__builtin_isgreaterequal", (main, node, loc, name) -> handleFloatBuiltinBinaryComparison(main, node,
				loc, name, IASTBinaryExpression.op_greaterEqual));
		fill(map, "__builtin_isless", (main, node, loc, name) -> handleFloatBuiltinBinaryComparison(main, node, loc,
				name, IASTBinaryExpression.op_lessThan));
		fill(map, "__builtin_islessequal", (main, node, loc, name) -> handleFloatBuiltinBinaryComparison(main, node,
				loc, name, IASTBinaryExpression.op_lessEqual));
		fill(map, "__builtin_isunordered", this::handleFloatBuiltinIsUnordered);
		fill(map, "__builtin_islessgreater", this::handleFloatBuiltinIsLessGreater);
		fill(map, "__builtin_constant_p", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 1,
				new CPrimitive(CPrimitives.BOOL)));
		fill(map, "__builtin_isinf_sign", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 1,
				new CPrimitive(CPrimitives.INT)));
		fill(map, "__builtin_isnan", (main, node, loc, name) -> handleUnaryFloatFunction(main, node, loc, "isnan"));

		/** math.h float functions **/
		// see 7.12.3.1 or http://en.cppreference.com/w/c/numeric/math/fpclassify
		fill(map, "fpclassify", this::handleUnaryFloatFunction);
		fill(map, "__fpclassify", this::handleUnaryFloatFunction); // ??
		fill(map, "__fpclassifyf", this::handleUnaryFloatFunction); // ??
		fill(map, "__fpclassifyl", this::handleUnaryFloatFunction); // ??

		// see 7.12.3.2 or http://en.cppreference.com/w/c/numeric/math/isfinite
		fill(map, "isfinite", this::handleUnaryFloatFunction);

		// see https://linux.die.net/man/3/finite (! NOT PART OF ANSI-C)
		fill(map, "finite", this::handleUnaryFloatFunction);
		fill(map, "__finite", this::handleUnaryFloatFunction);
		fill(map, "finitef", this::handleUnaryFloatFunction);
		fill(map, "__finitef", this::handleUnaryFloatFunction); // ??
		fill(map, "finitel", this::handleUnaryFloatFunction);
		fill(map, "__finitel", this::handleUnaryFloatFunction); // ??

		// see 7.12.3.3 or http://en.cppreference.com/w/c/numeric/math/isinf
		fill(map, "isinf", this::handleUnaryFloatFunction);
		fill(map, "__isinf", this::handleUnaryFloatFunction); // ??
		// see https://linux.die.net/man/3/finite (! NOT PART OF ANSI-C)
		fill(map, "isinff", this::handleUnaryFloatFunction);
		fill(map, "__isinff", this::handleUnaryFloatFunction); // ??
		fill(map, "isinfl", this::handleUnaryFloatFunction);
		fill(map, "__isinfl", this::handleUnaryFloatFunction); // ??

		// see 7.12.3.4 or http://en.cppreference.com/w/c/numeric/math/isnan
		fill(map, "isnan", this::handleUnaryFloatFunction);
		fill(map, "__isnan", this::handleUnaryFloatFunction); // ??
		// see https://linux.die.net/man/3/finite (! NOT PART OF ANSI-C)
		fill(map, "isnanf", this::handleUnaryFloatFunction);
		fill(map, "isnanl", this::handleUnaryFloatFunction);
		fill(map, "__isnanf", this::handleUnaryFloatFunction); // ??
		fill(map, "__isnanl", this::handleUnaryFloatFunction); // ??

		// see 7.12.3.5 or http://en.cppreference.com/w/c/numeric/math/isnormal
		fill(map, "isnormal", this::handleUnaryFloatFunction);

		// see 7.12.7.5 or http://en.cppreference.com/w/c/numeric/math/sqrt
		fill(map, "sqrt", this::handleUnaryFloatFunction);
		fill(map, "sqrtf", this::handleUnaryFloatFunction);
		fill(map, "sqrtl", this::handleUnaryFloatFunction);

		// see 7.12.7.2 or http://en.cppreference.com/w/c/numeric/math/fabs
		fill(map, "fabs", this::handleUnaryFloatFunction);
		fill(map, "fabsf", this::handleUnaryFloatFunction);
		fill(map, "fabsl", this::handleUnaryFloatFunction);

		// see 7.12.9.8 or http://en.cppreference.com/w/c/numeric/math/trunc
		fill(map, "trunc", this::handleUnaryFloatFunction);
		fill(map, "truncf", this::handleUnaryFloatFunction);
		fill(map, "truncl", this::handleUnaryFloatFunction);

		// see 7.12.9.6 or http://en.cppreference.com/w/c/numeric/math/round
		fill(map, "round", this::handleUnaryFloatFunction);
		fill(map, "roundf", this::handleUnaryFloatFunction);
		fill(map, "roundl", this::handleUnaryFloatFunction);
		// see 7.12.9.7 or http://en.cppreference.com/w/c/numeric/math/round
		fill(map, "lround", this::handleUnaryFloatFunction);
		fill(map, "lroundf", this::handleUnaryFloatFunction);
		fill(map, "lroundl", this::handleUnaryFloatFunction);
		fill(map, "llround", this::handleUnaryFloatFunction);
		fill(map, "llroundf", this::handleUnaryFloatFunction);
		fill(map, "llroundl", this::handleUnaryFloatFunction);

		// see 7.12.9.2 or http://en.cppreference.com/w/c/numeric/math/floor
		fill(map, "floor", this::handleUnaryFloatFunction);
		fill(map, "floorf", this::handleUnaryFloatFunction);
		fill(map, "floorl", this::handleUnaryFloatFunction);

		// see 7.12.9.1 or http://en.cppreference.com/w/c/numeric/math/ceil
		fill(map, "ceil", this::handleUnaryFloatFunction);
		fill(map, "ceilf", this::handleUnaryFloatFunction);
		fill(map, "ceill", this::handleUnaryFloatFunction);

		// see 7.12.12.2 or http://en.cppreference.com/w/c/numeric/math/fmax
		// NaN arguments are treated as missing data: if one argument is a NaN and the
		// other numeric, then the
		// fmin/fmax functions choose the numeric value.
		fill(map, "fmax", this::handleBinaryFloatFunction);
		fill(map, "fmaxf", this::handleBinaryFloatFunction);
		fill(map, "fmaxl", this::handleBinaryFloatFunction);

		// see 7.12.12.3 or http://en.cppreference.com/w/c/numeric/math/fmin
		fill(map, "fmin", this::handleBinaryFloatFunction);
		fill(map, "fminf", this::handleBinaryFloatFunction);
		fill(map, "fminl", this::handleBinaryFloatFunction);

		// see 7.12.10.2 or http://en.cppreference.com/w/c/numeric/math/remainder
		fill(map, "remainder", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 2,
				new CPrimitive(CPrimitives.DOUBLE)));
		fill(map, "remainderf", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 2,
				new CPrimitive(CPrimitives.FLOAT)));
		fill(map, "remainderl", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 2,
				new CPrimitive(CPrimitives.LONGDOUBLE)));

		// see 7.12.10.1 or http://en.cppreference.com/w/c/numeric/math/fmod
		fill(map, "fmod", this::handleBinaryFloatFunction);
		fill(map, "fmodf", this::handleBinaryFloatFunction);
		fill(map, "fmodl", this::handleBinaryFloatFunction);

		// see 7.12.11.1 or http://en.cppreference.com/w/c/numeric/math/copysign
		fill(map, "copysign", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 2,
				new CPrimitive(CPrimitives.DOUBLE)));
		fill(map, "copysignf", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 2,
				new CPrimitive(CPrimitives.FLOAT)));
		fill(map, "copysignl", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 2,
				new CPrimitive(CPrimitives.LONGDOUBLE)));

		// see 7.12.12.1 or https://en.cppreference.com/w/c/numeric/math/fdim
		fill(map, "fdim", this::handleBinaryFloatFunction);
		fill(map, "fdimf", this::handleBinaryFloatFunction);
		fill(map, "fdiml", this::handleBinaryFloatFunction);

		// 7.16 Variable arguments https://en.cppreference.com/w/c/variadic
		fill(map, "va_start", this::handleVaStart);
		fill(map, "__builtin_va_start", this::handleVaStart);
		fill(map, "va_end", this::handleVaEnd);
		fill(map, "__builtin_va_end", this::handleVaEnd);
		fill(map, "va_copy", this::handleVaCopy);
		fill(map, "__builtin_va_copy", this::handleVaCopy);

		// https://www.man7.org/linux/man-pages/man3/ffs.3.html
		fill(map, "ffs", (main, node, loc, name) -> handleFfs(main, node, loc, name, CPrimitives.INT));
		fill(map, "ffsl", (main, node, loc, name) -> handleFfs(main, node, loc, name, CPrimitives.LONG));
		fill(map, "ffsll", (main, node, loc, name) -> handleFfs(main, node, loc, name, CPrimitives.LONGLONG));

		/** SV-COMP and modeling functions **/
		fill(map, "__VERIFIER_ltl_step", (main, node, loc, name) -> handleLtlStep(main, node, loc));
		fill(map, "__VERIFIER_error", this::handleErrorFunction);
		fill(map, "reach_error", this::handleErrorFunction);

		fill(map, "__VERIFIER_assume", this::handleVerifierAssume);

		fill(map, "__VERIFIER_nondet_bool",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.BOOL)));
		fill(map, "__VERIFIER_nondet__Bool",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.BOOL)));
		fill(map, "__VERIFIER_nondet_char",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.CHAR)));
		fill(map, "__VERIFIER_nondet_pchar",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.CHAR)));
		fill(map, "__VERIFIER_nondet_float",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.FLOAT)));
		fill(map, "__VERIFIER_nondet_double",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.DOUBLE)));
		fill(map, "__VERIFIER_nondet_size_t",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.INT)));
		fill(map, "__VERIFIER_nondet_int",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.INT)));
		fill(map, "__VERIFIER_nondet_long",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.LONG)));
		fill(map, "__VERIFIER_nondet_longlong",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.LONGLONG)));
		fill(map, "__VERIFIER_nondet_int128",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.INT128)));
		fill(map, "__VERIFIER_nondet_loff_t",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.LONG)));
		fill(map, "__VERIFIER_nondet_short",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.SHORT)));
		fill(map, "__VERIFIER_nondet_pointer", (main, node, loc, name) -> handleVerifierNonDet(main, loc,
				new CPointer(new CPrimitive(CPrimitives.VOID))));
		fill(map, "__VERIFIER_nondet_uchar",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.UCHAR)));
		fill(map, "__VERIFIER_nondet_unsigned",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.UINT)));
		fill(map, "__VERIFIER_nondet_uint",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.UINT)));
		fill(map, "__VERIFIER_nondet_ulong",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.ULONG)));
		fill(map, "__VERIFIER_nondet_ulonglong",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.ULONGLONG)));
		fill(map, "__VERIFIER_nondet_uint128",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.UINT128)));
		fill(map, "__VERIFIER_nondet_ushort",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.USHORT)));

		fill(map, "__VERIFIER_atomic_begin", (main, node, loc, name) -> handleByFunctionCall(main, node, loc, name,
				new CPrimitive(CPrimitives.VOID)));
		fill(map, "__VERIFIER_atomic_end", (main, node, loc, name) -> handleByFunctionCall(main, node, loc, name,
				new CPrimitive(CPrimitives.VOID)));

		/** from assert.h */
		/** C standard library functions (from assert.h) to define the 'assert' macro */
		fill(map, "__assert_fail", this::handleAssertFail);
		fill(map, "__assert_func", this::handleAssertFail);
		// TODO: This should not occur in the preprocessed file, but we handle it for now
		fill(map, "assert", this::handleAssert);
		/** C11 static assertion (C language keyword, deprecated in C23) */
		fill(map, "_Static_assert", this::handleStaticAssert);
		/** C23 static assertion (C language keyword) */
		fill(map, "static_assert", this::handleStaticAssert);

		/** from fenv.h */
		fill(map, "fegetround", this::handleBuiltinFegetround);
		fill(map, "fesetround", this::handleBuiltinFesetround);

		/** Begin <stdlib.h> functions according to 7.22 General utilities <stdlib.h> **/
		/**
		 * 7.22.1 Numeric conversion functions
		 *
		 * 7.22.1.1 The atof function
		 *
		 * 7.22.1.2 The atoi, atol, and atoll functions
		 *
		 * The functions atof, atoi, atol, and atoll ... If the value of the result cannot be represented, the behavior
		 * is undefined.
		 *
		 * see https://en.cppreference.com/w/c/string/byte/atof
		 *
		 * double value corresponding to the contents of str on success. If the converted value falls out of range of
		 * the return type, the return value is undefined. If no conversion can be performed, 0.0 is returned.
		 *
		 * see https://en.cppreference.com/w/c/string/byte/atoi
		 *
		 * Integer value corresponding to the contents of str on success. If the converted value falls out of range of
		 * corresponding return type, the return value is undefined. If no conversion can be performed, ​0​ is returned.
		 *
		 * We handle this by overapproximation and do not check for undefined behavior.
		 */
		fill(map, "atof", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 1,
				new CPrimitive(CPrimitives.DOUBLE)));
		fill(map, "atoi", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 1,
				new CPrimitive(CPrimitives.INT)));
		fill(map, "atol", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 1,
				new CPrimitive(CPrimitives.LONG)));
		fill(map, "atoll", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 1,
				new CPrimitive(CPrimitives.LONGLONG)));

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
		fill(map, "strtof", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 2,
				new CPrimitive(CPrimitives.FLOAT)));
		fill(map, "strtod", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 2,
				new CPrimitive(CPrimitives.DOUBLE)));
		fill(map, "strtold", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 2,
				new CPrimitive(CPrimitives.LONGDOUBLE)));

		/**
		 * 7.22.2.1 The rand function
		 *
		 * see https://en.cppreference.com/w/c/numeric/random/rand
		 *
		 * Pseudo-random integer value between ​0​ and RAND_MAX, inclusive. The value of the RAND_MAX macro shall be at
		 * least 32767.
		 *
		 * We handle this similar to handleVerifierNonDet, but we limit the return type to positive range of int.
		 *
		 * We ignore seeding with srand.
		 */
		fill(map, "rand", this::handleRand);

		/**
		 * 7.22.2.2 The srand function
		 *
		 * see https://en.cppreference.com/w/c/numeric/random/srand
		 *
		 * The srand function uses the argument as a seed for a new sequence of pseudo-random numbers to be returned by
		 * subsequent calls to rand.
		 *
		 * We can safely skip this function.
		 */
		fill(map, "srand", (main, node, loc, name) -> handleVoidFunctionBySkipAndDispatch(main, node, loc, name, 1));

		/**
		 * 7.22.3 Memory management functions
		 *
		 * 7.22.3.1 The aligned_alloc function, 7.22.3.2 The calloc function, 7.22.3.3 The free function, 7.22.3.4 The
		 * malloc function, 7.22.3.5 The realloc function
		 */
		fill(map, "aligned_alloc", die);
		fill(map, "calloc", this::handleCalloc);
		fill(map, "free", this::handleFree);
		fill(map, "malloc", this::handleAlloc);
		fill(map, "realloc", this::handleRealloc);

		/**
		 * @formatter:off
		 * 7.22.4 Communication with the environment
		 *
		 * 7.22.4.1 The abort function
		 *   see https://en.cppreference.com/w/c/program/abort
		 * 7.22.4.2 The atexit function
		 * 7.22.4.3 The at_quick_exit function
		 * 7.22.4.4 The exit function
		 *   see https://en.cppreference.com/w/c/program/exit
		 * 7.22.4.5 The _Exit function
		 * 7.22.4.6 The getenv function
		 * 7.22.4.7 The quick_exit function
		 * 7.22.4.8 The system function
		 * @formatter:on
		 */
		fill(map, "abort", (main, node, loc, name) -> handleAbort(loc));
		fill(map, "exit", (main, node, loc, name) -> handleAbort(loc));
		fill(map, "atexit", die);
		fill(map, "at_quick_exit", die);
		fill(map, "_Exit", die);
		fill(map, "getenv", (main, node, loc, name) -> handleGetenv(main, node, loc));
		fill(map, "quick_exit", die);
		fill(map, "system", die);

		/**
		 * @formatter:off
		 * 7.22.5 Searching and sorting utilities
		 *
		 * 7.22.5.1 The bsearch function
		 * 7.22.5.2 The qsort function
		 * void qsort( void *ptr, size_t count, size_t size, int (*comp)(const void *, const void *) );
		 * @formatter:on
		 */
		fill(map, "bsearch", die);
		fill(map, "qsort", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 4,
				new CPointer(new CPrimitive(CPrimitives.VOID))));

		/**
		 * @formatter:off
		 * 7.22.6 Integer arithmetic functions
		 *
		 * 7.22.6.1 The abs, labs and llabs functions
		 * 7.22.6.2 The div, ldiv, and lldiv functions
		 * @formatter:on
		 */
		fill(map, "abs", (main, node, loc, name) -> handleAbs(main, node, loc, name, new CPrimitive(CPrimitives.INT)));
		fill(map, "labs",
				(main, node, loc, name) -> handleAbs(main, node, loc, name, new CPrimitive(CPrimitives.LONG)));
		fill(map, "llabs",
				(main, node, loc, name) -> handleAbs(main, node, loc, name, new CPrimitive(CPrimitives.LONGLONG)));
		fill(map, "imaxabs",
				(main, node, loc, name) -> handleAbs(main, node, loc, name, new CPrimitive(CPrimitives.LONGLONG)));
		fill(map, "div", die);
		fill(map, "ldiv", die);
		fill(map, "lldiv", die);

		/**
		 * @formatter:off
		 * 7.22.7 Multibyte/wide character conversion functions
		 *
		 * 7.22.7.1 The mblen function
		 * 7.22.7.2 The mbtowc function
		 * 7.22.7.3 The wctomb function
		 *
		 * @formatter:on
		 */
		fill(map, "mblen", die);
		fill(map, "mbtowc", die);
		fill(map, "wctomb", die);

		/**
		 * @formatter:off
		 * 7.22.8 Multibyte/wide string conversion functions
		 *
		 * 7.22.8.1 The mbstowcs function
		 * 7.22.8.2 The wcstombs function
		 * @formatter:on
		 */
		fill(map, "mbstowcs", die);
		fill(map, "wcstombs", die);

		// longjmp https://en.cppreference.com/w/c/program/longjmp
		// We cannot handle restoring the environment, so we just check if the function is reachable and create an
		// overraproximation for that case
		fill(map, "longjmp", (main, node, loc, name) -> handleUnsupportedFunctionByOverapproximation(main, loc, name,
				new CPrimitive(CPrimitives.VOID)));

		// setjmp https://en.cppreference.com/w/c/program/setjmp
		fill(map, "_setjmp", this::handleSetjmp);
		fill(map, "setjmp", this::handleSetjmp);

		// https://en.cppreference.com/w/c/chrono/time
		fill(map, "time", this::handleTime);

		// https://en.cppreference.com/w/c/string/wide/iswxdigit
		fill(map, "iswxdigit", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 1,
				new CPrimitive(CPrimitives.INT)));

		// https://refspecs.linuxbase.org/LSB_5.0.0/LSB-Core-generic/LSB-Core-generic/baselib---ctype-b-loc.html
		fill(map, "__ctype_b_loc", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 0,
				new CPointer(new CPointer(new CPrimitive(CPrimitives.SHORT)))));

		// TODO: These functions occur in SV-COMP, are they builtins?
		fill(map, "__bad_size_call_parameter",
				(main, node, loc, name) -> handleUnsupportedFunctionByOverapproximation(main, loc, name,
						new CPrimitive(CPrimitives.VOID)));
		fill(map, "__bad_percpu_size", (main, node, loc, name) -> handleUnsupportedFunctionByOverapproximation(main,
				loc, name, new CPrimitive(CPrimitives.VOID)));
		fill(map, "__bad_unaligned_access_size",
				(main, node, loc, name) -> handleUnsupportedFunctionByOverapproximation(main, loc, name,
						new CPrimitive(CPrimitives.VOID)));
		fill(map, "__xchg_wrong_size", (main, node, loc, name) -> handleUnsupportedFunctionByOverapproximation(main,
				loc, name, new CPrimitive(CPrimitives.VOID)));
		fill(map, "__xadd_wrong_size", (main, node, loc, name) -> handleUnsupportedFunctionByOverapproximation(main,
				loc, name, new CPrimitive(CPrimitives.VOID)));
		fill(map, "__cmpxchg_wrong_size", (main, node, loc, name) -> handleUnsupportedFunctionByOverapproximation(main,
				loc, name, new CPrimitive(CPrimitives.VOID)));
		fill(map, "__get_user_bad", (main, node, loc, name) -> handleUnsupportedFunctionByOverapproximation(main, loc,
				name, new CPrimitive(CPrimitives.VOID)));
		fill(map, "__put_user_bad", (main, node, loc, name) -> handleUnsupportedFunctionByOverapproximation(main, loc,
				name, new CPrimitive(CPrimitives.VOID)));

		/** End <stdlib.h> functions according to 7.22 General utilities <stdlib.h> **/

		checkFloatSupport(map, dieFloat);

		return Collections.unmodifiableMap(map);
	}

	private static void checkFloatSupport(final Map<String, IFunctionModelHandler> map,
			final IFunctionModelHandler dieFloat) {

		final List<String> declUnSupp = new ArrayList<>();
		final List<String> declNotSupp = new ArrayList<>();
		for (final String supportedFloatFunction : FloatSupportInUltimate.getSupportedFloatOperations()) {
			final IFunctionModelHandler fun = map.get(supportedFloatFunction);
			if (fun == dieFloat) {
				declUnSupp.add(supportedFloatFunction);
				continue;
			}
			if (fun == null) {
				declNotSupp.add(supportedFloatFunction);
				continue;
			}
		}

		if (!declUnSupp.isEmpty()) {
			throw new IllegalStateException("A supported float function is declared as unsupported: " + declUnSupp);
		}
		if (!declNotSupp.isEmpty()) {
			throw new IllegalStateException("A supported float function is not declared: " + declNotSupp);
		}
	}

	private Result handleGetenv(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc) {
		final var builder = new ExpressionResultBuilder();

		// dispatch the argument (unless it's a string literal, then we don't need it)
		assert node.getArguments().length == 1 : "unexpected number of arguments to getenv";
		final var arg = node.getArguments()[0];
		if (!isStringLiteral(arg)) {
			final var argRes = (ExpressionResult) main.dispatch(arg);
			builder.addAllExceptLrValue(argRes);
		}

		final var nondetString = getNondetStringOrNull(loc);
		builder.addAllExceptLrValue(nondetString).setLrValue(nondetString.getLrValue());

		return builder.build();
	}

	private ExpressionResult getNondetStringOrNull(final ILocation loc) {
		final var charType = new CPrimitive(CPrimitives.CHAR);
		final var sizeT = mTypeSizes.getSizeT();
		final var resultType = new CPointer(charType);
		final var builder = new ExpressionResultBuilder();

		final AuxVarInfo retvar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, resultType, SFO.AUXVAR.NONDET);
		builder.addDeclaration(retvar.getVarDec());
		builder.addAuxVar(retvar);
		builder.setLrValue(new LocalLValue(retvar.getLhs(), resultType, null));

		// one possible return value: NULL
		final var setPtrToNull = StatementFactory.constructSingleAssignmentStatement(loc, retvar.getLhs(),
				mExpressionTranslation.constructNullPointer(loc));

		// alternative option: return a nondeterministic string of nondeterministic length
		final AuxVarInfo len = mAuxVarInfoBuilder.constructAuxVarInfo(loc, sizeT, SFO.AUXVAR.NONDET);
		builder.addDeclaration(len.getVarDec());
		builder.addAuxVar(len);

		// allocate memory for a string and end it with a null-char as terminator
		final var body = new ArrayList<Statement>();
		body.add(new HavocStatement(loc, new VariableLHS[] { len.getLhs() }));
		body.add(new AssumeStatement(loc,
				mExpressionTranslation.constructBinaryComparisonExpression(loc, IASTBinaryExpression.op_greaterThan,
						len.getExp(), sizeT, mTypeSizes.constructLiteralForIntegerType(loc, sizeT, BigInteger.ZERO),
						sizeT)));
		body.add(mMemoryHandler.getUltimateMemAllocCall(len.getExp(), retvar.getLhs(), loc, MemoryArea.HEAP));
		final var nullChar = mTypeSizes.constructLiteralForIntegerType(loc, charType, BigInteger.ZERO);
		final var lenMinusOne = mExpressionTranslation.constructArithmeticIntegerExpression(loc,
				IASTBinaryExpression.op_minus, len.getExp(), sizeT,
				mTypeSizes.constructLiteralForIntegerType(loc, sizeT, BigInteger.ONE), sizeT);
		final var lastChar = MemoryHandler.constructPointerFromBaseAndOffset(
				MemoryHandler.getPointerBaseAddress(retvar.getExp(), loc), lenMinusOne, loc);
		body.addAll(mMemoryHandler.getWriteCall(loc,
				LRValueFactory.constructHeapLValue(mTypeHandler, lastChar, charType, null), nullChar, charType, false));

		final var stmt = StatementFactory.constructIfStatement(loc, new WildcardExpression(loc),
				new Statement[] { setPtrToNull }, body.toArray(Statement[]::new));
		builder.addStatement(stmt);

		return builder.build();
	}

	private List<Statement> makeVarargAssignment(final ILocation loc, final LRValue lhs, final Expression rhs) {
		if (lhs instanceof LocalLValue) {
			return List.of(StatementFactory.constructSingleAssignmentStatement(loc, ((LocalLValue) lhs).getLhs(), rhs));
		} else if (lhs instanceof HeapLValue) {
			return mMemoryHandler.getWriteCall(loc, (HeapLValue) lhs, rhs, lhs.getCType(), false);
		} else if (lhs instanceof RValue) {
			final RValue rValue = (RValue) lhs;
			return makeVarargAssignment(loc, new HeapLValue(rValue.getValue(), rValue.getCType(), null), rhs);
		} else {
			throw new UnsupportedOperationException("Unsupported type " + lhs.getClass().getSimpleName());
		}
	}

	private Result handleAtomicClear(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 2, name, arguments);
		final ExpressionResult write =
				mExprResultTransformer.dispatchPointerWrite(main, loc, arguments[0], mExpressionTranslation
						.constructLiteralForIntegerType(loc, new CPrimitive(CPrimitives.BOOL), BigInteger.ZERO));
		return applyMemoryOrder(loc, write, (ExpressionResult) main.dispatch(arguments[1]));
	}

	private Result handleAtomicTestAndSet(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 2, name, arguments);
		final CPrimitive boolType = new CPrimitive(CPrimitives.BOOL);
		final Expression value = mExpressionTranslation.constructLiteralForIntegerType(loc, boolType, BigInteger.ONE);
		final IASTNode target = arguments[0];
		final ExpressionResultBuilder builder =
				new ExpressionResultBuilder(mExprResultTransformer.dispatchPointerRead(main, loc, target));
		builder.addAllExceptLrValue(mExprResultTransformer.dispatchPointerWrite(main, loc, target, value));
		return applyMemoryOrder(loc, builder.build(), (ExpressionResult) main.dispatch(arguments[1]));
	}

	private Result handleAtomicLoad(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 3, name, arguments);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final ExpressionResult read = mExprResultTransformer.dispatchPointerRead(main, loc, arguments[0]);
		builder.addAllExceptLrValue(read);
		final ExpressionResult write =
				mExprResultTransformer.dispatchPointerWrite(main, loc, arguments[1], read.getLrValue().getValue());
		builder.addAllExceptLrValue(write);
		// Both the read and the write are atomic
		return applyMemoryOrder(loc, builder.build(), (ExpressionResult) main.dispatch(arguments[2]));
	}

	private Result handleAtomicStore(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 3, name, arguments);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final ExpressionResult read = mExprResultTransformer.dispatchPointerRead(main, loc, arguments[1]);
		builder.addAllExceptLrValue(read);
		// Make sure that only the write, but not the read is atomic
		final ExpressionResult write =
				mExprResultTransformer.dispatchPointerWrite(main, loc, arguments[0], read.getLrValue().getValue());
		builder.addAllExceptLrValue(applyMemoryOrder(loc, write, (ExpressionResult) main.dispatch(arguments[2])));
		return builder.build();
	}

	private Result handleAtomicExchange(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 4, name, arguments);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final ExpressionResult read1 = mExprResultTransformer.dispatchPointerRead(main, loc, arguments[0]);
		builder.addAllExceptLrValue(read1);
		builder.addAllExceptLrValue(
				mExprResultTransformer.dispatchPointerWrite(main, loc, arguments[2], read1.getLrValue().getValue()));
		final ExpressionResult read2 = mExprResultTransformer.dispatchPointerRead(main, loc, arguments[1]);
		builder.addAllExceptLrValue(read2);
		builder.addAllExceptLrValue(
				mExprResultTransformer.dispatchPointerWrite(main, loc, arguments[0], read2.getLrValue().getValue()));
		// All reads and writes are atomic
		return applyMemoryOrder(loc, builder.build(), (ExpressionResult) main.dispatch(arguments[3]));
	}

	private Result handleAtomicLoadN(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 2, name, arguments);
		return applyMemoryOrder(loc, mExprResultTransformer.dispatchPointerRead(main, loc, arguments[0]),
				(ExpressionResult) main.dispatch(arguments[1]));
	}

	private Result handleAtomicStoreN(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 3, name, arguments);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final ExpressionResult valueResult =
				mExprResultTransformer.transformDecaySwitch((ExpressionResult) main.dispatch(arguments[1]), loc, node);
		builder.addAllExceptLrValue(valueResult);
		// Make sure that only the write, but not the read is atomic
		builder.addAllExceptLrValue(applyMemoryOrder(loc, mExprResultTransformer.dispatchPointerWrite(main, loc,
				arguments[0], valueResult.getLrValue().getValue()), (ExpressionResult) main.dispatch(arguments[2])));
		return builder.build();
	}

	private Result handleAtomicExchangeN(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 3, name, arguments);
		final ExpressionResultBuilder builder =
				new ExpressionResultBuilder(mExprResultTransformer.dispatchPointerRead(main, loc, arguments[0]));
		final ExpressionResult valueResult =
				mExprResultTransformer.transformDecaySwitch((ExpressionResult) main.dispatch(arguments[1]), loc, node);
		builder.addAllExceptLrValue(valueResult);
		builder.addAllExceptLrValue(mExprResultTransformer.dispatchPointerWrite(main, loc, arguments[0],
				valueResult.getLrValue().getValue()));
		return applyMemoryOrder(loc, builder.build(), (ExpressionResult) main.dispatch(arguments[2]));
	}

	private Result handleAtomicFetch(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name, final int operator) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 3, name, arguments);
		final ExpressionResult operand =
				mExprResultTransformer.transformDecaySwitch((ExpressionResult) main.dispatch(arguments[1]), loc, node);
		final IASTNode target = arguments[0];
		final ExpressionResult read = mExprResultTransformer.dispatchPointerRead(main, loc, target);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder(read);
		final Expression newValue;
		final CPrimitive readType = (CPrimitive) read.getCType().getUnderlyingType();
		final CPrimitive operandType = (CPrimitive) operand.getCType().getUnderlyingType();
		if (operator == IASTBinaryExpression.op_plus || operator == IASTBinaryExpression.op_minus) {
			newValue = mExpressionTranslation.constructArithmeticExpression(loc, operator, read.getLrValue().getValue(),
					readType, operand.getLrValue().getValue(), operandType);
		} else {
			final ExpressionResult bitwiseResult =
					mExpressionTranslation.handleBinaryBitwiseExpression(loc, operator, read.getLrValue().getValue(),
							readType, operand.getLrValue().getValue(), operandType, mAuxVarInfoBuilder);
			builder.addAllExceptLrValue(bitwiseResult);
			newValue = bitwiseResult.getLrValue().getValue();
		}
		builder.addAllExceptLrValue(mExprResultTransformer.dispatchPointerWrite(main, loc, target, newValue));
		// Make sure that only the write, but not the read is atomic
		final ExpressionResult atomicBlock =
				applyMemoryOrder(loc, builder.build(), (ExpressionResult) main.dispatch(arguments[2]));
		return new ExpressionResultBuilder().addAllExceptLrValue(operand).addAllIncludingLrValue(atomicBlock).build();
	}

	/**
	 * Apply the {@code memoryOrder} to the {@code body} for stdatomic-library. If the memory order is equal to
	 * {@code MEMORY_ORDER_SEQ_CST}, we just make all statements atomic. For all other cases we just overapproximate
	 * (using an {@code assert false}), since we only support sequential consistency.
	 *
	 * @param loc
	 *            The C location
	 * @param body
	 *            The body that should be atomic based on the memory order
	 * @param memoryOrder
	 *            The memory order
	 * @return An ExpressionResult representing the translation respecting the memory order
	 */
	private ExpressionResult applyMemoryOrder(final ILocation loc, final ExpressionResult body,
			final ExpressionResult memoryOrder) {
		final ExpressionResultBuilder builder = new ExpressionResultBuilder(body);
		builder.resetStatements(List.of()).addAllExceptLrValue(memoryOrder);
		final CPrimitive intType = new CPrimitive(CPrimitives.INT);
		final Expression seqCst = mExpressionTranslation.constructLiteralForIntegerType(loc, intType,
				BigInteger.valueOf(MEMORY_ORDER_SEQ_CST));
		final Expression atomicCond = mExpressionTranslation.constructBinaryEqualityExpression(loc,
				IASTBinaryExpression.op_equals, memoryOrder.getLrValue().getValue(), intType, seqCst, intType);
		final Statement atomic = new AtomicStatement(loc, body.getStatements().toArray(Statement[]::new));
		final Statement overapproxAssert = new AssertStatement(loc, ExpressionFactory.createBooleanLiteral(loc, false));
		new Overapprox("memory order (only sequential consistency is supported)", loc).annotate(overapproxAssert);
		new Check(Spec.UNKNOWN).annotate(overapproxAssert);
		Statement statement;
		// Try to avoid unnecessary IfStatements
		if (atomicCond instanceof BooleanLiteral) {
			statement = ((BooleanLiteral) atomicCond).getValue() ? atomic : overapproxAssert;
		} else {
			statement =
					new IfStatement(loc, atomicCond, new Statement[] { atomic }, new Statement[] { overapproxAssert });
		}
		return builder.addStatement(statement).build();
	}

	private Result handleVaStart(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 2, name, arguments);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final ExpressionResult arg0 = (ExpressionResult) main.dispatch(arguments[0]);
		builder.addAllExceptLrValue(arg0);
		// The second argument of va_start has to be the rightmost fixed parameter
		// (according to the C standard section 7.16.1.3.4). Therefore we simply dispatch it here.
		builder.addAllExceptLrValue((ExpressionResult) main.dispatch(arguments[1]));
		final String procedure = mProcedureManager.getCurrentProcedureID();
		final IdentifierExpression rhs = new IdentifierExpression(loc, mTypeHandler.getBoogiePointerType(), SFO.VARARGS,
				new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, procedure));
		return builder.addStatements(makeVarargAssignment(loc, arg0.getLrValue(), rhs)).build();
	}

	private Result handleVaEnd(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 1, name, arguments);

		final ExpressionResult pRex =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);

		final ExpressionResultBuilder resultBuilder =
				new ExpressionResultBuilder().addAllExceptLrValue(pRex).setLrValue(pRex.getLrValue());

		// Translate va_end(valist) to ULTIMATE.dealloc({ base: valist!base, offset: 0 }) to ensure the memory to be
		// freed
		final Expression zero = mExpressionTranslation.constructLiteralForIntegerType(loc,
				mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);
		final Expression pointerWithoutOffset = MemoryHandler.constructPointerFromBaseAndOffset(
				MemoryHandler.getPointerBaseAddress(pRex.getLrValue().getValue(), loc), zero, loc);
		final RValue value = new RValue(pointerWithoutOffset, pRex.getCType());

		/*
		 * Add checks for validity of the to be freed pointer if required.
		 */
		resultBuilder.addStatements(mMemoryHandler.getChecksForFreeCall(loc, value));

		/*
		 * Add a call to our internal deallocation procedure Ultimate.dealloc
		 */
		final CallStatement deallocCall = mMemoryHandler.getDeallocCall(value, loc);
		resultBuilder.addStatement(deallocCall);

		return resultBuilder.build();
	}

	/**
	 * Translate va_copy(dst, src) to a simple overapproximation that simply havocs dst (and annotates it with
	 * "overapproximation")
	 */
	private Result handleVaCopy(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 2, name, arguments);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final ExpressionResult dst = (ExpressionResult) main.dispatch(arguments[0]);
		builder.addAllExceptLrValue(dst);
		builder.addAllExceptLrValue((ExpressionResult) main.dispatch(arguments[1]));
		final AuxVarInfo auxVarInfo = mAuxVarInfoBuilder.constructAuxVarInfo(loc,
				new CPointer(new CPrimitive(CPrimitives.CHAR)), AUXVAR.NONDET);
		builder.addAuxVar(auxVarInfo);
		builder.addDeclaration(auxVarInfo.getVarDec());
		final List<Statement> writes = makeVarargAssignment(loc, dst.getLrValue(), auxVarInfo.getExp());
		writes.forEach(new Overapprox(name, loc)::annotate);
		return builder.addStatements(writes).build();
	}

	private Result handleFfs(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name, final CPrimitives argPrimitive) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 1, name, arguments);
		final ExpressionResult argResult =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);

		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		builder.addAllExceptLrValue(argResult);

		final var resultType = new CPrimitive(CPrimitives.INT);
		final AuxVarInfo resultInfo = mAuxVarInfoBuilder.constructAuxVarInfo(loc, resultType, AUXVAR.NONDET);
		builder.addDeclaration(resultInfo.getVarDec());
		builder.addAuxVar(resultInfo);

		final int argSize = mTypeSizes.getSize(argPrimitive);
		final var argType = new CPrimitive(argPrimitive);

		final var argZero = mExpressionTranslation.constructZero(loc, argType);
		final var argIsZero = mExpressionTranslation.constructBinaryEqualityExpression(loc,
				IASTBinaryExpression.op_equals, argResult.getLrValue().getValue(), argType, argZero, argType);

		final Statement[] caseZero, caseNonZero;
		{
			// Case "zero": argument is 0, and so is the return value
			final var resultZero = mExpressionTranslation.constructZero(loc, resultType);
			final var resultIsZero = mExpressionTranslation.constructBinaryEqualityExpression(loc,
					IASTBinaryExpression.op_equals, resultInfo.getExp(), resultType, resultZero, resultType);
			caseZero = new AssumeStatement[] { new AssumeStatement(loc, resultIsZero) };
		}
		{
			final ArrayList<Statement> statements = new ArrayList<>();

			// 1 <= result <= argSize*8
			final var resultOne =
					mExpressionTranslation.constructLiteralForIntegerType(loc, resultType, BigInteger.ONE);
			final long bitsPerByte = 8L;
			final var sizeExp = mExpressionTranslation.constructLiteralForIntegerType(loc, resultType,
					BigInteger.valueOf(argSize * bitsPerByte));
			final var resultInRange = ExpressionFactory.and(loc, List.of(
					mExpressionTranslation.constructBinaryComparisonIntegerExpression(loc,
							IASTBinaryExpression.op_lessEqual, resultOne, resultType, resultInfo.getExp(), resultType),
					mExpressionTranslation.constructBinaryComparisonIntegerExpression(loc,
							IASTBinaryExpression.op_lessEqual, resultInfo.getExp(), resultType, sizeExp, resultType)));
			statements.add(new AssumeStatement(loc, resultInRange));

			// expression "~0", which is 11...111 in binary.
			final var allOnes = mExpressionTranslation.constructUnaryExpression(loc, IASTUnaryExpression.op_tilde,
					argZero, argType);

			// 0 != arg & (1 << (result-1))
			// This means that at index "result", the argument has a 1.
			final var lShiftRes = mExpressionTranslation.handleBitshiftExpression(loc,
					IASTBinaryExpression.op_shiftLeft,
					mExpressionTranslation.constructLiteralForIntegerType(loc, argType, BigInteger.ONE), argType,
					mExpressionTranslation.constructArithmeticIntegerExpression(loc, IASTBinaryExpression.op_minus,
							resultInfo.getExp(), resultType, resultOne, resultType),
					resultType, mAuxVarInfoBuilder);
			builder.addAllExceptLrValueAndStatements(lShiftRes);
			statements.addAll(lShiftRes.getStatements());
			final var andRes1 = mExpressionTranslation.handleBinaryBitwiseExpression(loc,
					IASTBinaryExpression.op_binaryAnd, argResult.getLrValue().getValue(), argType,
					lShiftRes.getLrValue().getValue(), argType, mAuxVarInfoBuilder);
			builder.addAllExceptLrValueAndStatements(andRes1);
			statements.addAll(andRes1.getStatements());
			final var resultBitIsSet = mExpressionTranslation.constructBinaryEqualityExpression(loc,
					IASTBinaryExpression.op_notequals, argZero, argType, andRes1.getLrValue().getValue(), argType);
			statements.add(new AssumeStatement(loc, resultBitIsSet));

			// 0 == arg & (~0 >> |arg|-(result-1))
			// This means that at all lower indices than "result", the argument has only zeroes.
			final var rShiftRes = mExpressionTranslation.handleBitshiftExpression(loc,
					IASTBinaryExpression.op_shiftRight, allOnes, argType,
					mExpressionTranslation.constructArithmeticIntegerExpression(loc, IASTBinaryExpression.op_minus,
							sizeExp, resultType,
							mExpressionTranslation.constructArithmeticIntegerExpression(loc,
									IASTBinaryExpression.op_minus, resultInfo.getExp(), resultType, resultOne,
									resultType),
							resultType),
					resultType, mAuxVarInfoBuilder);
			builder.addAllExceptLrValueAndStatements(rShiftRes);
			statements.addAll(rShiftRes.getStatements());
			final var andRes2 = mExpressionTranslation.handleBinaryBitwiseExpression(loc,
					IASTBinaryExpression.op_binaryAnd, argResult.getLrValue().getValue(), argType,
					rShiftRes.getLrValue().getValue(), argType, mAuxVarInfoBuilder);
			builder.addAllExceptLrValueAndStatements(andRes2);
			statements.addAll(andRes2.getStatements());
			final var firstSetBit = mExpressionTranslation.constructBinaryEqualityExpression(loc,
					IASTBinaryExpression.op_equals, argZero, argType, andRes2.getLrValue().getValue(), argType);
			statements.add(new AssumeStatement(loc, firstSetBit));

			caseNonZero = statements.toArray(Statement[]::new);
		}

		builder.addStatement(new IfStatement(loc, argIsZero, caseZero, caseNonZero));
		builder.setLrValue(new LocalLValue(resultInfo.getLhs(), resultType, null));

		return builder.build();
	}

	private Result handleAbs(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name, final CPrimitive resultType) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 1, name, arguments);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final ExpressionResult argResult =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		builder.addAllExceptLrValue(argResult);
		final Expression expr = argResult.getLrValue().getValue();
		// abs(MIN_INT) does overflow, so add an assertion for overflow checking
		if (mSettings.checkSignedIntegerBounds() && resultType.isIntegerType() && !mTypeSizes.isUnsigned(resultType)) {
			final Expression minInt = mTypeSizes.constructLiteralForIntegerType(loc, resultType,
					mTypeSizes.getMinValueOfPrimitiveType(resultType));
			final Expression biggerMinInt = mExpressionTranslation.constructBinaryComparisonExpression(loc,
					IASTBinaryExpression.op_greaterThan, expr, resultType, minInt, resultType);
			final AssertStatement biggerMinIntStmt = new AssertStatement(loc, biggerMinInt);
			new Check(Spec.INTEGER_OVERFLOW).annotate(biggerMinIntStmt);
			builder.addStatement(biggerMinIntStmt);
		}
		// Construct if x > 0 then x else -x as LrValue for abs(x)
		final Expression positive = mExpressionTranslation.constructBinaryComparisonExpression(loc,
				IASTBinaryExpression.op_greaterThan, expr, resultType,
				mTypeSizes.constructLiteralForIntegerType(loc, resultType, BigInteger.ZERO), resultType);
		final Expression negated =
				mExpressionTranslation.constructUnaryExpression(loc, IASTUnaryExpression.op_minus, expr, resultType);
		final Expression iteExpression = ExpressionFactory.constructIfThenElseExpression(loc, positive, expr, negated);
		return builder.setLrValue(new RValue(iteExpression, resultType)).build();
	}

	// For now we do not handle setjmp properly. We crash on longjmp, so it is sufficient to always return 0 for setjmp.
	private Result handleSetjmp(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		final CPrimitive returnType = new CPrimitive(CPrimitives.INT);
		return new ExpressionResult(new RValue(
				mExpressionTranslation.constructLiteralForIntegerType(loc, returnType, BigInteger.ZERO), returnType));
	}

	// Overapproximates sprintf as follows:
	// ctr:=0; while (*) { havoc aux; *(ptr+ctr) := aux; ctr := ctr + 1; }
	private Result handleSPrintF(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc) {
		final IASTInitializerClause[] arguments = node.getArguments();
		assert arguments.length >= 1 : "insufficient arguments to snprintf";
		final var builder = new ExpressionResultBuilder();

		final Overapprox overAppFlag = new Overapprox("snprintf", loc);
		builder.addOverapprox(overAppFlag);

		// first argument is ptr
		final var ptr = mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		builder.addAllExceptLrValue(ptr);

		// dispatch remaining arguments (except for string literals)
		for (int i = 1; i < arguments.length; ++i) {
			if (isStringLiteral(arguments[i])) {
				continue;
			}
			final ExpressionResult argRes =
					mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[i]);
			builder.addAllExceptLrValue(argRes);
		}

		// declare loop counter ctr
		final AuxVarInfo ctr = mAuxVarInfoBuilder.constructAuxVarInfo(loc,
				mExpressionTranslation.getCTypeOfPointerComponents(), SFO.AUXVAR.LOOPCTR);
		builder.addDeclaration(ctr.getVarDec());
		builder.addAuxVar(ctr);

		// declare nondet aux var
		final AuxVarInfo auxvar =
				mAuxVarInfoBuilder.constructAuxVarInfo(loc, new CPrimitive(CPrimitives.CHAR), SFO.AUXVAR.NONDET);
		builder.addDeclaration(auxvar.getVarDec());
		builder.addAuxVar(auxvar);

		// ctr := 0
		final var zero = mTypeSizes.constructLiteralForIntegerType(loc,
				mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);
		final var initCtr = StatementFactory.constructSingleAssignmentStatement(loc, ctr.getLhs(), zero);
		builder.addStatement(initCtr);

		final var body = new ArrayList<Statement>();

		// havoc aux;
		final var havocNondet = new HavocStatement(loc, new VariableLHS[] { auxvar.getLhs() });
		body.add(havocNondet);

		// *(ptr + ctr) := aux
		final var ptrOffset = MemoryHandler.getPointerOffset(ptr.getLrValue().getValue(), loc);
		final Expression newOffset = mExpressionTranslation.constructArithmeticExpression(loc,
				IASTBinaryExpression.op_plus, ptrOffset, mExpressionTranslation.getCTypeOfPointerComponents(),
				ctr.getExp(), mExpressionTranslation.getCTypeOfPointerComponents());
		final var ptrPlusCtr = MemoryHandler.constructPointerFromBaseAndOffset(
				MemoryHandler.getPointerBaseAddress(ptr.getLrValue().getValue(), loc), newOffset, loc);
		final var ptrPlusCtrHlv = LRValueFactory.constructHeapLValue(mTypeHandler, ptrPlusCtr, ptr.getCType(), null);
		final var writeToMem = mMemoryHandler.getWriteCall(loc, ptrPlusCtrHlv, auxvar.getExp(),
				new CPrimitive(CPrimitives.CHAR), false);
		for (final var write : writeToMem) {
			overAppFlag.annotate(write);
		}
		body.addAll(writeToMem);
		if (mDataRaceChecker != null) {
			mDataRaceChecker.checkOnWrite(builder, loc, ptrPlusCtrHlv);
		}

		// ctr := ctr + 1
		final var incrementCtr = StatementFactory.constructSingleAssignmentStatement(loc, ctr.getLhs(),
				mExpressionTranslation.constructArithmeticIntegerExpression(loc, IASTBinaryExpression.op_plus,
						ctr.getExp(), mExpressionTranslation.getCTypeOfPointerComponents(),
						mTypeSizes.constructLiteralForIntegerType(loc,
								mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ONE),
						mExpressionTranslation.getCTypeOfPointerComponents()));
		body.add(incrementCtr);

		final var loop = new WhileStatement(loc, new WildcardExpression(loc), new LoopInvariantSpecification[0],
				body.toArray(Statement[]::new));
		builder.addStatement(loop);

		final var ret =
				mAuxVarInfoBuilder.constructAuxVarInfo(loc, new CPrimitive(CPrimitives.CHAR), SFO.AUXVAR.RETURNED);
		builder.addAuxVar(ret);
		builder.addDeclaration(ret.getVarDec());
		builder.setLrValue(new LocalLValue(ret.getLhs(), new CPrimitive(CPrimitives.CHAR), null));

		return builder.build();
	}

	// Overapproximates snprintf as follows:
	// ctr:=0; while (*) { assume ctr < len; havoc aux; *(ptr+ctr) := aux; ctr := ctr + 1; }
	private Result handleSnPrintF(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc) {
		final IASTInitializerClause[] arguments = node.getArguments();
		assert arguments.length >= 2 : "insufficient arguments to snprintf";
		final var builder = new ExpressionResultBuilder();

		final Overapprox overAppFlag = new Overapprox("snprintf", loc);
		builder.addOverapprox(overAppFlag);

		// first argument is ptr
		final var ptr = mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		builder.addAllExceptLrValue(ptr);

		// second argument is len
		final var len = mExprResultTransformer.transformDispatchDecaySwitchImplicitConversion(main, loc, arguments[1],
				mExpressionTranslation.getCTypeOfPointerComponents());
		builder.addAllExceptLrValue(len);

		// dispatch remaining arguments (except for string literals)
		for (int i = 2; i < arguments.length; ++i) {
			if (isStringLiteral(arguments[i])) {
				continue;
			}
			final ExpressionResult argRes =
					mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[i]);
			builder.addAllExceptLrValue(argRes);
		}

		// declare loop counter ctr
		final AuxVarInfo ctr = mAuxVarInfoBuilder.constructAuxVarInfo(loc,
				mExpressionTranslation.getCTypeOfPointerComponents(), SFO.AUXVAR.LOOPCTR);
		builder.addDeclaration(ctr.getVarDec());
		builder.addAuxVar(ctr);

		// declare nondet aux var
		final AuxVarInfo auxvar =
				mAuxVarInfoBuilder.constructAuxVarInfo(loc, new CPrimitive(CPrimitives.CHAR), SFO.AUXVAR.NONDET);
		builder.addDeclaration(auxvar.getVarDec());
		builder.addAuxVar(auxvar);

		// ctr := 0
		final var zero = mTypeSizes.constructLiteralForIntegerType(loc,
				mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);
		final var initCtr = StatementFactory.constructSingleAssignmentStatement(loc, ctr.getLhs(), zero);
		builder.addStatement(initCtr);

		final var body = new ArrayList<Statement>();

		// assume ctr < len;
		final var assumeInRange = new AssumeStatement(loc,
				mExpressionTranslation.constructBinaryComparisonIntegerExpression(loc, IASTBinaryExpression.op_lessThan,
						ctr.getExp(), mExpressionTranslation.getCTypeOfPointerComponents(), len.getLrValue().getValue(),
						mExpressionTranslation.getCTypeOfPointerComponents()));
		body.add(assumeInRange);

		// havoc aux;
		final var havocNondet = new HavocStatement(loc, new VariableLHS[] { auxvar.getLhs() });
		body.add(havocNondet);

		// *(ptr + ctr) := aux
		final var ptrOffset = MemoryHandler.getPointerOffset(ptr.getLrValue().getValue(), loc);
		final Expression newOffset = mExpressionTranslation.constructArithmeticExpression(loc,
				IASTBinaryExpression.op_plus, ptrOffset, mExpressionTranslation.getCTypeOfPointerComponents(),
				ctr.getExp(), mExpressionTranslation.getCTypeOfPointerComponents());
		final var ptrPlusCtr = MemoryHandler.constructPointerFromBaseAndOffset(
				MemoryHandler.getPointerBaseAddress(ptr.getLrValue().getValue(), loc), newOffset, loc);
		final var ptrPlusCtrHlv = LRValueFactory.constructHeapLValue(mTypeHandler, ptrPlusCtr, ptr.getCType(), null);
		final var writeToMem = mMemoryHandler.getWriteCall(loc, ptrPlusCtrHlv, auxvar.getExp(),
				new CPrimitive(CPrimitives.CHAR), false);
		for (final var write : writeToMem) {
			overAppFlag.annotate(write);
		}
		body.addAll(writeToMem);
		if (mDataRaceChecker != null) {
			mDataRaceChecker.checkOnWrite(builder, loc, ptrPlusCtrHlv);
		}

		// ctr := ctr + 1
		final var incrementCtr = StatementFactory.constructSingleAssignmentStatement(loc, ctr.getLhs(),
				mExpressionTranslation.constructArithmeticIntegerExpression(loc, IASTBinaryExpression.op_plus,
						ctr.getExp(), mExpressionTranslation.getCTypeOfPointerComponents(),
						mTypeSizes.constructLiteralForIntegerType(loc,
								mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ONE),
						mExpressionTranslation.getCTypeOfPointerComponents()));
		body.add(incrementCtr);

		final var loop = new WhileStatement(loc, new WildcardExpression(loc), new LoopInvariantSpecification[0],
				body.toArray(Statement[]::new));
		builder.addStatement(loop);

		final var ret =
				mAuxVarInfoBuilder.constructAuxVarInfo(loc, new CPrimitive(CPrimitives.CHAR), SFO.AUXVAR.RETURNED);
		builder.addAuxVar(ret);
		builder.addDeclaration(ret.getVarDec());
		builder.setLrValue(new LocalLValue(ret.getLhs(), new CPrimitive(CPrimitives.CHAR), null));

		return builder.build();
	}

	/**
	 * Handles all derivates of *scanf as an overapproximation by writing non-deterministic values to all arguments
	 * starting from {@code firstArgumentToWrite}.
	 */
	// TODO Frank 2022-11-14: In general this is unsound since scanf can write multiple bytes. E.g. for the format %2c
	// we would need two writes, for the format %s even non-determinstically many writes! Determining whether this
	// occurs in the format, is only possible if the format is a literal (it can be any expression in general).
	private Result handleScanf(final String name, final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final int firstArgumentToWrite) {
		// The application is only marked as an overapproximation, if we read from a string.
		final boolean markAsOverapproximation = name.startsWith("sscanf") || name.startsWith("swscanf");
		final IASTInitializerClause[] arguments = node.getArguments();
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();

		for (int i = 0; i < arguments.length; i++) {
			if (i < firstArgumentToWrite && isStringLiteral(arguments[i])) {
				// Don't dispatch string literals
				continue;
			}
			final ExpressionResult arg =
					mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[i]);
			builder.addAllExceptLrValue(arg);
			if (i < firstArgumentToWrite) {
				continue;
			}

			final CType type = ((CPointer) arg.getCType()).getPointsToType();
			final AuxVarInfo auxvar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, type, SFO.AUXVAR.NONDET);
			builder.addDeclaration(auxvar.getVarDec());
			builder.addAuxVar(auxvar);

			// Write a non-deterministic value to the given address, but make sure the value is in range
			final var lValue =
					LRValueFactory.constructHeapLValue(mTypeHandler, arg.getLrValue().getValue(), type, null);
			mExpressionTranslation.addAssumeValueInRangeStatements(loc, auxvar.getExp(), type, builder);
			final List<Statement> writes = mMemoryHandler.getWriteCall(loc, lValue, auxvar.getExp(), type, false);
			if (markAsOverapproximation) {
				writes.forEach(new Overapprox(name, loc)::annotate);
			}
			builder.addStatements(writes);

			if (mDataRaceChecker != null) {
				mDataRaceChecker.checkOnWrite(builder, loc, lValue);
			}
		}

		// The number of arguments to which sth should be written is returned.
		// Therefore we create a fresh variable and assume that it is in the desired range
		// (0 to the number of variables written to)
		final CPrimitive retValueType = new CPrimitive(CPrimitives.LONG);
		final AuxVarInfo returnAuxVar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, retValueType, SFO.AUXVAR.NONDET);
		builder.addAuxVar(returnAuxVar);
		builder.addDeclaration(returnAuxVar.getVarDec());
		final var minValue = mExpressionTranslation.constructLiteralForIntegerType(loc, retValueType, BigInteger.ZERO);
		final var retVal = returnAuxVar.getExp();
		final var greaterMin = mExpressionTranslation.constructBinaryComparisonExpression(loc,
				IASTBinaryExpression.op_lessEqual, minValue, retValueType, retVal, retValueType);
		final int writtenArgs = arguments.length - firstArgumentToWrite;
		final var maxValue = mExpressionTranslation.constructLiteralForIntegerType(loc, retValueType,
				BigInteger.valueOf(writtenArgs));
		final var smallerMax = mExpressionTranslation.constructBinaryComparisonExpression(loc,
				IASTBinaryExpression.op_lessEqual, retVal, retValueType, maxValue, retValueType);
		builder.addStatement(new AssumeStatement(loc, ExpressionFactory.and(loc, List.of(greaterMin, smallerMax))));
		builder.setLrValue(new RValue(retVal, retValueType));
		if (markAsOverapproximation) {
			builder.addOverapprox(new Overapprox(name, loc));
		}

		return builder.build();
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
		builder.addDeclaration(auxvarinfo.getVarDec());
		builder.addAuxVar(auxvarinfo);

		final Overapprox overAppFlag = new Overapprox(name, loc);
		builder.addOverapprox(overAppFlag);
		final RValue lrVal = new RValue(auxvarinfo.getExp(), resultType);
		builder.setLrValue(lrVal);
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
		resultBuilder.addDeclaration(auxvarinfo.getVarDec());
		resultBuilder.addAuxVar(auxvarinfo);
		resultBuilder.addStatement(call);
		resultBuilder.setLrValue(new RValue(auxvarinfo.getExp(), new CPointer(new CPrimitive(CPrimitives.VOID))));

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
		builder.addDeclaration(auxvarinfo.getVarDec());
		builder.addAuxVar(auxvarinfo);

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
		builder.addDeclaration(auxvarinfo.getVarDec());
		builder.addAuxVar(auxvarinfo);

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

	private Result handleTime(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 1, name, arguments);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		// TODO: Also write the return value to the pointer, if it is not NULL
		builder.addAllExceptLrValue((ExpressionResult) main.dispatch(arguments[0]));
		builder.addAllIncludingLrValue(handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.LONG)));
		return builder.build();
	}

	/**
	 * TODO pthread support
	 */
	private Result handlePthread_create(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 4, name, arguments);

		final ExpressionResultBuilder builder = new ExpressionResultBuilder();

		final ExpressionResult argThreadAttributes =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[1]);
		final ExpressionResult argStartRoutine =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[2]);
		final ExpressionResult startRoutineArguments;
		{
			final ExpressionResult tmp =
					mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[3]);
			startRoutineArguments = mExprResultTransformer.performImplicitConversion(tmp,
					new CPointer(new CPrimitive(CPrimitives.VOID)), loc);
		}
		builder.addAllExceptLrValue(argThreadAttributes, argStartRoutine, startRoutineArguments);

		final String methodName = getForkedProcedure(node, arguments[2], argStartRoutine);
		final CFunction function = mProcedureManager.getCFunctionType(methodName);
		final int params = function.getParameterTypes().length;
		final Expression[] forkArguments;
		if (params == 0) {
			forkArguments = new Expression[0];
		} else if (params == 1) {
			forkArguments = new Expression[] { startRoutineArguments.getLrValue().getValue() };
		} else {
			throw new UnsupportedSyntaxException(loc, "pthread_create calls function with more than one argument");
		}

		final Expression[] threadId = mThreadIdManager.updateForkedThreadId(arguments[0], main, loc, node, builder);
		final ForkStatement fs = new ForkStatement(loc, threadId, methodName, forkArguments);
		mProcedureManager.registerForkStatement(fs);
		builder.addStatement(fs);

		final boolean letPthreadCreateAlwaysReturnZero = false;
		final CPrimitive returnValueCType = new CPrimitive(CPrimitive.CPrimitives.INT);
		final Expression returnValue;
		if (letPthreadCreateAlwaysReturnZero) {
			returnValue = mTypeSizes.constructLiteralForIntegerType(loc, returnValueCType, BigInteger.ZERO);
		} else {
			// auxvar for fork return value (status code)
			final AuxVarInfo auxvarinfo =
					mAuxVarInfoBuilder.constructAuxVarInfo(loc, returnValueCType, SFO.AUXVAR.NONDET);
			builder.addDeclaration(auxvarinfo.getVarDec());
			builder.addAuxVar(auxvarinfo);
			returnValue = auxvarinfo.getExp();
		}
		final LRValue val = new RValue(returnValue, returnValueCType);

		builder.setLrValue(val);
		return builder.build();
	}

	private String getForkedProcedure(final IASTFunctionCallExpression node, final IASTInitializerClause argument,
			final ExpressionResult argStartRoutine) {
		final String methodName;
		{
			// We hope that the function is not given by a function pointer that is stored
			// in a variable but directly by the function name
			final String rawProcName;
			if (argument instanceof CASTIdExpression) {
				final CASTIdExpression castIdExpr = (CASTIdExpression) argument;
				rawProcName = castIdExpr.getName().toString();
			} else if (argument instanceof CASTUnaryExpression) {
				final CASTUnaryExpression castUnaryExpr = (CASTUnaryExpression) argument;
				if (castUnaryExpr.getOperator() != IASTUnaryExpression.op_amper) {
					throw new UnsupportedOperationException(
							"Third argument of pthread_create is: " + argument.getClass().getSimpleName());
				}
				// function foo is probably given as a function pointer of the form & foo
				if (!(castUnaryExpr.getOperand() instanceof CASTIdExpression)) {
					throw new UnsupportedOperationException("Third argument of pthread_create is: "
							+ castUnaryExpr.getOperand().getClass().getSimpleName());
				}
				final CASTIdExpression castIdExpr = (CASTIdExpression) castUnaryExpr.getOperand();
				rawProcName = castIdExpr.getName().toString();
			} else {
				throw new UnsupportedOperationException(
						"Third argument of pthread_create is " + argument.getClass().getSimpleName());
			}

			final String multiParseProcedureName =
					mSymboltable.applyMultiparseRenaming(node.getContainingFilename(), rawProcName);
			if (!mProcedureManager.hasProcedure(multiParseProcedureName)) {
				throw new UnsupportedOperationException("cannot find function " + multiParseProcedureName
						+ " Ultimate does not support pthread_create in combination with function pointers");
			}

			final IdentifierExpression idExpr = (IdentifierExpression) argStartRoutine.getLrValue().getValue();
			final String prefix = idExpr.getIdentifier().substring(0, 9);
			if (!prefix.equals(SFO.FUNCTION_ADDRESS)) {
				throw new UnsupportedOperationException("unable to decode " + idExpr.getIdentifier());
			}
			methodName = idExpr.getIdentifier().substring(9);
		}
		return methodName;
	}

	// We assume success and return 0 without any additional checks.
	private Result handlePthread_success(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		builder.setLrValue(new RValue(
				mTypeSizes.constructLiteralForIntegerType(loc, new CPrimitive(CPrimitives.INT), BigInteger.ZERO),
				new CPrimitive(CPrimitives.INT)));
		return builder.build();
	}

	/**
	 * TODO pthread support
	 */
	private Result handlePthread_join(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {

		// get arguments
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 2, name, arguments);

		// Object that will build our result
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final Expression[] threadId = mThreadIdManager.getJoinedThreadId(arguments[0], main, loc, builder);

		final LRValue argAddressOfResultPointerLr;
		{
			// final ExpressionResult tmp = mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main,
			// loc, arguments[1]);
			final ExpressionResult tmp = (ExpressionResult) main.dispatch(arguments[1]);
			final ExpressionResult argAddressOfResultPointer = mExprResultTransformer.performImplicitConversion(tmp,
					new CPointer(new CPrimitive(CPrimitives.VOID)), loc);
			builder.addAllExceptLrValue(argAddressOfResultPointer);
			argAddressOfResultPointerLr = argAddressOfResultPointer.getLrValue();
		}

		final JoinStatement js;
		if (argAddressOfResultPointerLr.isNullPointerConstant()) {
			js = new JoinStatement(loc, threadId, new VariableLHS[0]);
			builder.addStatement(js);
		} else {
			// auxvar for joined procedure's return value
			final CType cType = new CPointer(new CPrimitive(CPrimitives.VOID));
			final AuxVarInfo auxvarinfo = mAuxVarInfoBuilder.constructAuxVarInfo(loc, cType, SFO.AUXVAR.NONDET);
			builder.addDeclaration(auxvarinfo.getVarDec());
			builder.addAuxVar(auxvarinfo);
			js = new JoinStatement(loc, threadId, new VariableLHS[] { auxvarinfo.getLhs() });
			builder.addStatement(js);
			final HeapLValue heapLValue;
			if (argAddressOfResultPointerLr instanceof HeapLValue) {
				heapLValue = (HeapLValue) argAddressOfResultPointerLr;
			} else {
				heapLValue = LRValueFactory.constructHeapLValue(mTypeHandler, argAddressOfResultPointerLr.getValue(),
						cType, false, null);
			}
			final List<Statement> wc = mMemoryHandler.getWriteCall(loc, heapLValue, auxvarinfo.getExp(), cType, false);
			builder.addStatements(wc);
		}
		// we assume that this function is always successful and returns 0
		builder.setLrValue(new RValue(
				mTypeSizes.constructLiteralForIntegerType(loc, new CPrimitive(CPrimitives.INT), BigInteger.ZERO),
				new CPrimitive(CPrimitives.INT)));
		return builder.build();
	}

	private Result handlePthread_exit(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		mMemoryHandler.requireMemoryModelFeature(MemoryModelDeclarations.ULTIMATE_PTHREADS_MUTEX);

		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 1, name, arguments);

		final ExpressionResult arg =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		final ExpressionResult transformedArg = mExprResultTransformer.performImplicitConversion(arg,
				new CPointer(new CPrimitive(CPrimitives.VOID)), loc);

		final IBoogieType type = mTypeHandler.getBoogiePointerType();
		final String identifier = SFO.RES;
		final DeclarationInformation declarationInformation = new DeclarationInformation(
				StorageClass.IMPLEMENTATION_OUTPARAM, mProcedureManager.getCurrentProcedureID());
		final LeftHandSide[] lhs =
				new LeftHandSide[] { new VariableLHS(loc, type, identifier, declarationInformation) };
		final AssignmentStatement retValAssignment =
				new AssignmentStatement(loc, lhs, new Expression[] { transformedArg.getLrValue().getValue() });
		final ExpressionResultBuilder erb = new ExpressionResultBuilder();
		erb.addAllExceptLrValue(transformedArg);
		erb.addStatement(retValAssignment);
		erb.addStatement(new ReturnStatement(loc));

		return erb.build();
	}

	/**
	 * Implements handing for pthread_cond_wait. Since spurious wake-ups are possible (and covered by SVCOMP
	 * benchmarks), we do not actually wait. We merely unlock and lock the mutex.
	 */
	private Result handlePthread_cond_wait(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {

		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 2, name, arguments);

		final ExpressionResultBuilder builder = new ExpressionResultBuilder();

		final ExpressionResult unlock = createPthread_mutex_unlock(main, loc, arguments[1]);
		builder.addAllExceptLrValue(unlock);

		final ExpressionResult lock = createPthread_mutex_lock(main, loc, arguments[1]);
		builder.addAllExceptLrValue(lock);

		builder.setLrValue(new RValue(
				mTypeSizes.constructLiteralForIntegerType(loc, new CPrimitive(CPrimitives.INT), BigInteger.ZERO),
				new CPrimitive(CPrimitives.INT)));
		return builder.build();
	}

	/**
	 * We assume that the mutex type is PTHREAD_MUTEX_NORMAL which means that if we lock a mutex that that is already
	 * locked, then the thread blocks.
	 */
	private Result handlePthread_mutex_lock(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		return handleLockCall(main, node, loc, name, mMemoryHandler::constructPthreadMutexLockCall);
	}

	/**
	 * We assume that the mutex type is PTHREAD_MUTEX_NORMAL which means that if we unlock a mutex that has never been
	 * locked, the behavior is undefined. We use a semantics where unlocking a non-locked mutex is a no-op. For the
	 * return value we follow what GCC did in my experiments. It produced code that returned 0 even if we unlocked a
	 * non-locked mutex.
	 */
	private Result handlePthread_mutex_unlock(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		return handleLockCall(main, node, loc, name, mMemoryHandler::constructPthreadMutexUnlockCall);
	}

	private Result handlePthread_mutex_trylock(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		return handleLockCall(main, node, loc, name, mMemoryHandler::constructPthreadMutexTryLockCall);
	}

	private Result handlePthread_rwlock_rdlock(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		return handleLockCall(main, node, loc, name, mMemoryHandler::constructPthreadRwLockReadLockCall);
	}

	private Result handlePthread_rwlock_wrlock(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		return handleLockCall(main, node, loc, name, mMemoryHandler::constructPthreadRwLockWriteLockCall);
	}

	private Result handlePthread_rwlock_unlock(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		return handleLockCall(main, node, loc, name, mMemoryHandler::constructPthreadRwLockUnlockCall);
	}

	private ExpressionResult createPthread_mutex_lock(final IDispatcher main, final ILocation loc,
			final IASTInitializerClause mutex) {
		return handleLockCall(main, loc, "pthread_mutex_lock", mutex, mMemoryHandler::constructPthreadMutexLockCall);
	}

	private ExpressionResult createPthread_mutex_unlock(final IDispatcher main, final ILocation loc,
			final IASTInitializerClause mutex) {
		return handleLockCall(main, loc, "pthread_mutex_unlock", mutex,
				mMemoryHandler::constructPthreadMutexUnlockCall);
	}

	private ExpressionResult handleLockCall(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name, final ILockCallFactory callFactory) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 1, name, arguments);
		final IASTInitializerClause lock = arguments[0];

		return handleLockCall(main, loc, name, lock, callFactory);
	}

	private ExpressionResult handleLockCall(final IDispatcher main, final ILocation loc, final String name,
			final IASTInitializerClause lock, final ILockCallFactory callFactory) {
		final ExpressionResultBuilder erb = new ExpressionResultBuilder();

		final ExpressionResult arg = mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, lock);
		final Expression index = arg.getLrValue().getValue();
		erb.addAllExceptLrValue(arg);

		// auxvar for procedure's return value
		final CType cType = new CPrimitive(CPrimitives.INT);
		final AuxVarInfo auxvarinfo = mAuxVarInfoBuilder.constructAuxVarInfo(loc, cType, SFO.AUXVAR.NONDET);
		erb.addDeclaration(auxvarinfo.getVarDec());
		erb.addAuxVar(auxvarinfo);

		erb.addStatement(callFactory.apply(loc, index, auxvarinfo.getLhs()));
		erb.setLrValue(new RValue(auxvarinfo.getExp(), new CPrimitive(CPrimitives.INT)));
		return erb.build();
	}

	private interface ILockCallFactory {
		Statement apply(ILocation loc, Expression index, VariableLHS lhs);
	}

	private Result handlePthread_mutex_init(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		mMemoryHandler.requireMemoryModelFeature(MemoryModelDeclarations.ULTIMATE_PTHREADS_MUTEX);

		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 2, name, arguments);

		final ExpressionResult arg1 =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		final ExpressionResult arg2 =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[1]);
		final boolean isNullPointerLiteral = mMemoryHandler.isNullPointerLiteral(arg2.getLrValue().getValue());
		if (!isNullPointerLiteral) {
			final String msg = "The second argument of the pthread_mutex_init is not a null pointer. This means that "
					+ "non-default attributes are used. We support only the default attributes.";
			throw new UnsupportedSyntaxException(loc, msg);
		}

		final CPrimitive returnType = new CPrimitive(CPrimitives.INT);
		// we assume that function is always successful and returns 0
		final BigInteger value = BigInteger.ZERO;
		final Expression index = arg1.getLrValue().getValue();
		final AssignmentStatement unlockMutex = mMemoryHandler.constructMutexArrayAssignment(loc, index, false);
		final ExpressionResultBuilder erb = new ExpressionResultBuilder();
		erb.addAllExceptLrValue(arg1);
		erb.addStatement(unlockMutex);
		erb.setLrValue(new RValue(mTypeSizes.constructLiteralForIntegerType(loc, returnType, value),
				new CPrimitive(CPrimitives.INT)));
		return erb.build();
	}

	private static Result handleBuiltinUnreachable(final ILocation loc) {
		/*
		 * https://gcc.gnu.org/onlinedocs/gcc/Other-Builtins.html
		 *
		 * Built-in Function: void __builtin_unreachable (void)
		 *
		 * If control flow reaches the point of the __builtin_unreachable, the program is undefined. It is useful in
		 * situations where the compiler cannot deduce the unreachability of the code.
		 */

		// TODO: Add option that allows us to check for builtin_unreachable by adding assert
		// return new ExpressionResult(Collections.singletonList(new AssertStatement(loc,
		// new de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral(loc, false))), null);
		// TODO: Add option that just ignores the function:
		// return new SkipResult();
		// TODO: Keep the following code, but add it as option together with the other two
		return new ExpressionResult(
				Collections.singletonList(new AssumeStatement(loc, ExpressionFactory.createBooleanLiteral(loc, false))),
				null);
	}

	private Result handleAssertFail(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {

		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 4, name, arguments);

		final List<ExpressionResult> argDispatchResults = new ArrayList<>();
		for (final IASTInitializerClause argument : arguments) {
			argDispatchResults.add((ExpressionResult) main.dispatch(argument));
		}

		final ExpressionResultBuilder erb = new ExpressionResultBuilder().addAllExceptLrValue(argDispatchResults);
		return erb.addStatement(createAnnotatedAssertOrAssume(loc, name, mSettings.checkAssertions(), Spec.ASSERT,
				ExpressionFactory.createBooleanLiteral(loc, false))).build();
	}

	private Result handleAssert(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {

		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 1, name, arguments);

		final ExpressionResult result = mExprResultTransformer
				.transformSwitchRexIntToBool((ExpressionResult) main.dispatch(arguments[0]), loc, node);
		return new ExpressionResultBuilder().addAllExceptLrValue(result).addStatement(createAnnotatedAssertOrAssume(loc,
				name, mSettings.checkAssertions(), Spec.ASSERT, result.getLrValue().getValue())).build();
	}

	/**
	 * Handle C11 or C23 static assertions with or without an explicit message.
	 *
	 * @param main
	 *            the current dispatcher
	 * @param node
	 *            the static assert expression
	 * @param loc
	 *            the location of the static assert
	 * @param name
	 *            the name of the method
	 *
	 * @return {@link ExpressionResult} representing the static assertion
	 */
	private Result handleStaticAssert(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {

		final IASTInitializerClause[] arguments = node.getArguments();
		final int numAssertArgs = arguments.length;

		/* check if signature of assertion is of form 'static_assert(expr)' or 'static_assert(expr, msg)' */
		if (numAssertArgs == 2) {
			/* static C11 or C23 assertion with two arguments (expr and msg) */
			checkArguments(loc, 2, name, arguments);

			if (isStringLiteral(arguments[1])) {
				/* extract string literal value for custom error message */
				final String errorMsg = String.valueOf(((IASTLiteralExpression) arguments[1]).getValue());

				final ExpressionResult result = mExprResultTransformer
						.transformSwitchRexIntToBool((ExpressionResult) main.dispatch(arguments[0]), loc, node);
				return new ExpressionResultBuilder()
						.addAllExceptLrValue(result).addStatement(createAnnotatedAssertOrAssume(loc, name,
								mSettings.checkAssertions(), Spec.ASSERT, result.getLrValue().getValue(), errorMsg))
						.build();
			}
			/* WARNING: this case should be never reached since the msg should be always a string literal */
			throw new IncorrectSyntaxException(loc, "Message parameter of static assert is not a string literal");
		}
		/* static C11 or C23 assertion with one argument (expr) */
		checkArguments(loc, 1, name, arguments);

		/* handle as regular assertion */
		return handleAssert(main, node, loc, name);
	}

	private Result handleBuiltinFegetround(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {

		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 0, name, arguments);
		final RValue rvalue = mExpressionTranslation.constructBuiltinFegetround(loc);

		return new ExpressionResultBuilder().setLrValue(rvalue).build();
	}

	private Result handleBuiltinFesetround(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {

		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 1, name, arguments);

		final ExpressionResult decayedArgument =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		final ExpressionResult convertedArgument =
				mExprResultTransformer.convertIfNecessary(loc, decayedArgument, new CPrimitive(CPrimitives.INT));
		final ExpressionResult arg = convertedArgument;

		return mExpressionTranslation.constructBuiltinFesetround(loc, (RValue) arg.getLrValue(), mAuxVarInfoBuilder);
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

		final CPointer voidPointerType = new CPointer(new CPrimitive(CPrimitives.VOID));
		final AuxVarInfo auxvar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, voidPointerType, SFO.AUXVAR.MEMSETRES);
		result.addDeclaration(auxvar.getVarDec());
		result.addAuxVar(auxvar);

		result.addStatement(mMemoryHandler.constructUltimateMemsetCall(loc, dispatchedArgS.getLrValue().getValue(),
				convertedArgC.getLrValue().getValue(), convertedArgN.getLrValue().getValue(), auxvar.getLhs()));
		return result.build();
	}

	private Result handleCalloc(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		/*
		 * C11 says in 7.22.3.2 void *calloc(size_t nmemb, size_t size); The calloc function allocates space for an
		 * array of nmemb objects, each of whose size is size. The space is initialized to all bits zero.
		 */
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 2, name, arguments);

		final ExpressionResult nmemb = mExprResultTransformer.transformDispatchDecaySwitchImplicitConversion(main, loc,
				arguments[0], mTypeSizeComputer.getSizeT());
		final ExpressionResult size = mExprResultTransformer.transformDispatchDecaySwitchImplicitConversion(main, loc,
				arguments[1], mTypeSizeComputer.getSizeT());

		final Expression product = mExpressionTranslation.constructArithmeticExpression(loc,
				IASTBinaryExpression.op_multiply, nmemb.getLrValue().getValue(), mTypeSizeComputer.getSizeT(),
				size.getLrValue().getValue(), mTypeSizeComputer.getSizeT());
		final ExpressionResultBuilder result = new ExpressionResultBuilder().addAllExceptLrValue(nmemb, size);

		final CPointer resultType = new CPointer(new CPrimitive(CPrimitives.VOID));
		final AuxVarInfo auxvar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, resultType, SFO.AUXVAR.MALLOC);
		result.addDeclaration(auxvar.getVarDec());
		result.addStatement(mMemoryHandler.getUltimateMemAllocCall(product, auxvar.getLhs(), loc, MemoryArea.HEAP));
		result.addStatement(mMemoryHandler.constructUltimateMeminitCall(loc, nmemb.getLrValue().getValue(),
				size.getLrValue().getValue(), product, auxvar.getExp()));
		result.setLrValue(new RValue(auxvar.getExp(), resultType));
		return result.build();
	}

	/**
	 * Translates free(e) by creating a function call expression for the ~free(e) function and declaring its usage in
	 * the memory model.
	 */
	private Result handleFree(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 1, name, arguments);

		final ExpressionResult pRex =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);

		final ExpressionResultBuilder resultBuilder =
				new ExpressionResultBuilder().addAllExceptLrValue(pRex).setLrValue(pRex.getLrValue());

		/*
		 * Add checks for validity of the to be freed pointer if required.
		 */
		resultBuilder.addStatements(mMemoryHandler.getChecksForFreeCall(loc, (RValue) pRex.getLrValue()));

		/*
		 * Add a call to our internal deallocation procedure Ultimate.dealloc
		 */
		final CallStatement deallocCall = mMemoryHandler.getDeallocCall(pRex.getLrValue(), loc);
		resultBuilder.addStatement(deallocCall);

		return resultBuilder.build();
	}

	private Result handleAlloc(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String methodName) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 1, methodName, arguments);

		final ExpressionResult exprRes =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		final ExpressionResult exprResConverted =
				mExprResultTransformer.performImplicitConversion(exprRes, mTypeSizeComputer.getSizeT(), loc);
		final ExpressionResultBuilder erb = new ExpressionResultBuilder().addAllExceptLrValue(exprResConverted);
		final CPointer resultType = new CPointer(new CPrimitive(CPrimitives.VOID));
		final AuxVarInfo auxvar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, resultType, SFO.AUXVAR.MALLOC);
		erb.addDeclaration(auxvar.getVarDec());
		erb.addAuxVar(auxvar);

		final MemoryArea memArea;
		if (methodName.equals("malloc")) {
			memArea = MemoryArea.HEAP;
		} else if (methodName.equals("alloca") || methodName.equals("__builtin_alloca")) {
			memArea = MemoryArea.STACK;
		} else {
			throw new IllegalArgumentException("unknown allocation method; " + methodName);
		}
		erb.addStatement(mMemoryHandler.getUltimateMemAllocCall(exprResConverted.getLrValue().getValue(),
				auxvar.getLhs(), loc, memArea));
		erb.setLrValue(new RValue(auxvar.getExp(), resultType));

		// for alloc a we have to free the variable ourselves when the
		// stackframe is closed, i.e. at a return
		if ("alloca".equals(methodName) || "__builtin_alloca".equals(methodName)) {
			final LocalLValue llVal = new LocalLValue(auxvar.getLhs(), resultType, null);
			mMemoryHandler.addVariableToBeFreed(
					new LocalLValueILocationPair(llVal, LocationFactory.createIgnoreLocation(loc)));
			// we need to clear auxVars because otherwise the malloc auxvar is havocced after
			// this, and free (triggered by the statement before) would fail.
			erb.clearAuxVars();
		}
		return erb.build();
	}

	/**
	 *
	 * signature: void *realloc(void *ptr, size_t size);
	 *
	 * for reference: C11 7.22.3.5
	 *
	 * @param main
	 * @param node
	 * @param loc
	 * @param methodName
	 * @return
	 */
	private Result handleRealloc(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String methodName) {
		final MemoryModelDeclarations reallocMmDecl = MemoryModelDeclarations.C_REALLOC;

		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 2, methodName, arguments);

		final CType voidPointerType = new CPointer(new CPrimitive(CPrimitives.VOID));
		final ExpressionResult ptr = mExprResultTransformer.transformDispatchDecaySwitchImplicitConversion(main, loc,
				arguments[0], voidPointerType);

		final ExpressionResult size = mExprResultTransformer.transformDispatchDecaySwitchImplicitConversion(main, loc,
				arguments[1], mTypeSizeComputer.getSizeT());

		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
		resultBuilder.addAllExceptLrValue(ptr);
		resultBuilder.addAllExceptLrValue(size);

		final AuxVarInfo auxvarinfo =
				mAuxVarInfoBuilder.constructAuxVarInfo(loc, ptr.getLrValue().getCType(), SFO.AUXVAR.REALLOCRES);

		final CallStatement call = StatementFactory.constructCallStatement(loc, false,
				new VariableLHS[] { auxvarinfo.getLhs() }, reallocMmDecl.getName(),
				new Expression[] { ptr.getLrValue().getValue(), size.getLrValue().getValue() });

		resultBuilder.addDeclaration(auxvarinfo.getVarDec());
		resultBuilder.addAuxVar(auxvarinfo);
		resultBuilder.addStatement(call);
		resultBuilder.setLrValue(new RValue(auxvarinfo.getExp(), new CPointer(new CPrimitive(CPrimitives.VOID))));

		// add marker for global declaration to memory handler
		mMemoryHandler.requireMemoryModelFeature(reallocMmDecl);

		// add required information to function handler.
		mProcedureManager.registerProcedure(reallocMmDecl.getName());

		return resultBuilder.build();
	}

	private Result handleBuiltinExpect(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		/**
		 * Built-in Function: long __builtin_expect (long exp, long c)
		 *
		 * You may use __builtin_expect to provide the compiler with branch prediction information. In general, you
		 * should prefer to use actual profile feedback for this (-fprofile-arcs), as programmers are notoriously bad at
		 * predicting how their programs actually perform. However, there are applications in which this data is hard to
		 * collect.
		 *
		 * The return value is the value of exp, which should be an integral expression. The semantics of the built-in
		 * are that it is expected that exp == c. For example:
		 *
		 * <code>if (__builtin_expect (x, 0)) foo ();</code>
		 *
		 * indicates that we do not expect to call foo, since we expect x to be zero. Since you are limited to integral
		 * expressions for exp, you should use constructions such as
		 *
		 * <code>if (__builtin_expect (ptr != NULL, 1)) foo (*ptr);</code>
		 *
		 * when testing pointer or floating-point values.
		 */
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 2, name, arguments);
		final ExpressionResult arg1 =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		final ExpressionResult arg2 =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[1]);
		return new ExpressionResultBuilder().addAllExceptLrValue(arg1, arg2).setLrValue(arg1.getLrValue()).build();
	}

	private static ExpressionResult handleAbort(final ILocation loc) {
		return new ExpressionResult(
				Collections.singletonList(new AssumeStatement(loc, ExpressionFactory.createBooleanLiteral(loc, false))),
				null);
	}

	private ExpressionResult handleVerifierNonDet(final IDispatcher main, final ILocation loc, final CType cType) {
		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
		final AuxVarInfo auxvarinfo = mAuxVarInfoBuilder.constructAuxVarInfo(loc, cType, SFO.AUXVAR.NONDET);
		resultBuilder.addDeclaration(auxvarinfo.getVarDec());
		resultBuilder.addAuxVar(auxvarinfo);
		if (HAVOC_NONDET_AUXVARS_ALSO_BEFORE) {
			resultBuilder.addStatement(new HavocStatement(loc, new VariableLHS[] { auxvarinfo.getLhs() }));
		}
		final LRValue returnValue = new RValue(auxvarinfo.getExp(), cType);
		resultBuilder.setLrValue(returnValue);
		mExpressionTranslation.addAssumeValueInRangeStatements(loc, returnValue.getValue(), returnValue.getCType(),
				resultBuilder);

		assert CTranslationUtil.isAuxVarMapComplete(mNameHandler, resultBuilder.getDeclarations(),
				resultBuilder.getAuxVars());
		return resultBuilder.build();
	}

	private Result handleRand(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		checkArguments(loc, 0, name, node.getArguments());

		final CPrimitive cType = new CPrimitive(CPrimitives.INT);
		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
		final AuxVarInfo auxvarinfo = mAuxVarInfoBuilder.constructAuxVarInfo(loc, cType, SFO.AUXVAR.NONDET);
		resultBuilder.addDeclaration(auxvarinfo.getVarDec());
		resultBuilder.addAuxVar(auxvarinfo);

		final LRValue returnValue = new RValue(auxvarinfo.getExp(), cType);
		resultBuilder.setLrValue(returnValue);

		final Expression expr = returnValue.getValue();
		final Expression minValue = mTypeSizes.constructLiteralForIntegerType(loc, cType, BigInteger.ZERO);
		final Expression maxValue =
				mTypeSizes.constructLiteralForIntegerType(loc, cType, mTypeSizes.getMaxValueOfPrimitiveType(cType));

		final Expression biggerMinInt = mExpressionTranslation.constructBinaryComparisonExpression(loc,
				IASTBinaryExpression.op_lessEqual, minValue, cType, expr, cType);
		final Expression smallerMaxValue = mExpressionTranslation.constructBinaryComparisonExpression(loc,
				IASTBinaryExpression.op_lessEqual, expr, cType, maxValue, cType);
		final AssumeStatement inRange = new AssumeStatement(loc, ExpressionFactory.newBinaryExpression(loc,
				BinaryExpression.Operator.LOGICAND, biggerMinInt, smallerMaxValue));
		resultBuilder.addStatement(inRange);

		assert CTranslationUtil.isAuxVarMapComplete(mNameHandler, resultBuilder.getDeclarations(),
				resultBuilder.getAuxVars());
		return resultBuilder.build();
	}

	private Result handleVerifierAssume(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		// according to SV-Comp specification assume takes only one argument, but the code allows more than one
		checkArguments(loc, 1, name, node.getArguments());

		final List<Expression> args = new ArrayList<>();
		final List<ExpressionResult> results = new ArrayList<>();
		for (final IASTInitializerClause inParam : node.getArguments()) {
			ExpressionResult in = mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, inParam);
			if (in.getLrValue().getValue() == null) {
				final String msg = "Incorrect or invalid in-parameter! " + loc.toString();
				throw new IncorrectSyntaxException(loc, msg);
			}
			in = mExprResultTransformer.rexIntToBool(in, loc);
			args.add(in.getLrValue().getValue());
			results.add(in);
		}

		final ExpressionResultBuilder rtr = new ExpressionResultBuilder().addAllExceptLrValue(results);
		for (final Expression a : args) {
			// could just take the first as there is only one, but it's so easy to make it more general..
			rtr.addStatement(new AssumeStatement(loc, a));
		}
		assert CTranslationUtil.isAuxVarMapComplete(mNameHandler, rtr.getDeclarations(), rtr.getAuxVars());
		return rtr.build();
	}

	private Result handleNaNOrInfinity(final ILocation loc, final String methodName) {
		return mExpressionTranslation.createNanOrInfinity(loc, methodName);
	}

	private Result handleUnaryFloatFunction(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final FloatFunction floatFunction = FloatFunction.decode(name);
		final ExpressionResult arg = handleFloatArguments(main, node, loc, name, 1, floatFunction).get(0);
		final RValue rvalue =
				mExpressionTranslation.constructOtherUnaryFloatOperation(loc, floatFunction, (RValue) arg.getLrValue());
		return new ExpressionResultBuilder().addAllExceptLrValue(arg).setLrValue(rvalue).build();
	}

	private Result handleBinaryFloatFunction(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final FloatFunction floatFunction = FloatFunction.decode(name);
		final List<ExpressionResult> args = handleFloatArguments(main, node, loc, name, 2, floatFunction);
		final RValue rvalue = mExpressionTranslation.constructOtherBinaryFloatOperation(loc, floatFunction,
				(RValue) args.get(0).getLrValue(), (RValue) args.get(1).getLrValue());
		return new ExpressionResultBuilder().addAllExceptLrValue(args).setLrValue(rvalue).build();
	}

	private List<ExpressionResult> handleFloatArguments(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name, final int numberOfArgs, final FloatFunction floatFunction) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, numberOfArgs, name, arguments);
		if (floatFunction == null) {
			throw new IllegalArgumentException(
					"Ultimate declared float handling for " + name + ", but is not known float function");
		}
		final List<ExpressionResult> rtr = new ArrayList<>();
		for (final IASTInitializerClause argument : arguments) {
			final ExpressionResult decayedArgument =
					mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, argument);
			final ExpressionResult convertedArgument =
					mExprResultTransformer.convertIfNecessary(loc, decayedArgument, floatFunction.getType());
			rtr.add(convertedArgument);
		}

		final CPrimitive typeDeterminedByName = floatFunction.getType();
		if (typeDeterminedByName != null) {
			final List<ExpressionResult> newRtr = new ArrayList<>();
			for (final ExpressionResult arg : rtr) {
				newRtr.add(mExprResultTransformer.convertIfNecessary(loc, arg, typeDeterminedByName));
			}
			return newRtr;
		}
		return rtr;
	}

	private Result handleFloatBuiltinBinaryComparison(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name, final int op) {
		/*
		 * Handle the following float comparisons
		 *
		 * http://en.cppreference.com/w/c/numeric/math/isless
		 *
		 * http://en.cppreference.com/w/c/numeric/math/islessequal
		 *
		 * http://en.cppreference.com/w/c/numeric/math/isgreater
		 *
		 * http://en.cppreference.com/w/c/numeric/math/isgreaterequal
		 *
		 */
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 2, name, arguments);

		final ExpressionResult rl =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		final ExpressionResult rr =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[1]);

		// Note: this works because SMTLIB already ensures that all comparisons return false if one of the arguments is
		// NaN

		return mCEpressionTranslator.handleRelationalOperators(loc, op, rl, rr);
	}

	/**
	 * Handle the following macro. <code>int isunordered (real-floating x, real-floating y)</code>
	 *
	 * This macro determines whether its arguments are unordered. It is 1 if x or y are NaN, and 0 otherwise.
	 *
	 * According to 7.12.14.6 of C11 the isunordered macro returns 1 if its arguments are unordered and 0 otherwise. The
	 * meaning of "unordered" is defined in 7.12.14. Two floating point values are unordered if at least one of the two
	 * is a NaN value.
	 *
	 * See also http://en.cppreference.com/w/c/numeric/math/isunordered
	 *
	 */
	private Result handleFloatBuiltinIsUnordered(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 2, name, arguments);

		final ExpressionResult leftRvaluedResult =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		final ExpressionResult rightRvaluedResult =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[1]);
		final ExpressionResult nanLResult =
				mExpressionTranslation.createNan(loc, (CPrimitive) leftRvaluedResult.getLrValue().getCType());
		final ExpressionResult nanRResult =
				mExpressionTranslation.createNan(loc, (CPrimitive) rightRvaluedResult.getLrValue().getCType());
		final Expression leftExpr = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ,
				leftRvaluedResult.getLrValue().getValue(), nanLResult.getLrValue().getValue());
		final Expression rightExpr = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ,
				rightRvaluedResult.getLrValue().getValue(), nanRResult.getLrValue().getValue());
		final Expression expr = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, leftExpr, rightExpr);
		final LRValue lrVal = new RValue(expr, new CPrimitive(CPrimitives.INT), true);
		final ExpressionResult rtr = new ExpressionResultBuilder()
				.addAllExceptLrValue(leftRvaluedResult, rightRvaluedResult, nanLResult, nanRResult).setLrValue(lrVal)
				.build();
		assert CTranslationUtil.isAuxVarMapComplete(mNameHandler, rtr.getDeclarations(), rtr.getAuxVars());
		return rtr;
	}

	private Result handleFloatBuiltinIsLessGreater(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		/*
		 * http://en.cppreference.com/w/c/numeric/math/islessgreater
		 *
		 * int islessgreater (real-floating x, real-floating y)
		 *
		 * This macro determines whether the argument x is less or greater than y.
		 *
		 * It is equivalent to (x) < (y) || (x) > (y) (although it only evaluates x and y once), but no exception is
		 * raised if x or y are NaN.
		 *
		 * This macro is not equivalent to x != y, because that expression is true if x or y are NaN.
		 *
		 * Note: I did not find any reference as to how often x and y are evaluated; it seems this can actually evaluate
		 * x and y twice.
		 */

		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 2, name, arguments);

		ExpressionResult leftOp =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		ExpressionResult rightOp =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[1]);
		final Pair<ExpressionResult, ExpressionResult> newOps =
				mExprResultTransformer.usualArithmeticConversions(loc, leftOp, rightOp);
		leftOp = newOps.getFirst();
		rightOp = newOps.getSecond();

		final ExpressionResult lessThan =
				mCEpressionTranslator.handleRelationalOperators(loc, IASTBinaryExpression.op_lessThan, leftOp, rightOp);
		final ExpressionResult greaterThan = mCEpressionTranslator.handleRelationalOperators(loc,
				IASTBinaryExpression.op_greaterThan, leftOp, rightOp);

		final Expression expr = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR,
				lessThan.getLrValue().getValue(), greaterThan.getLrValue().getValue());
		final LRValue lrVal = new RValue(expr, new CPrimitive(CPrimitives.INT), true);
		final ExpressionResult rtr =
				new ExpressionResultBuilder().addAllExceptLrValue(lessThan, greaterThan).setLrValue(lrVal).build();
		assert CTranslationUtil.isAuxVarMapComplete(mNameHandler, rtr.getDeclarations(), rtr.getAuxVars());
		return rtr;
	}

	private Result handleBuiltinObjectSize(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		// DD: builtin-object size is way more complicated that the old implementation!
		// Read https://gcc.gnu.org/onlinedocs/gcc/Object-Size-Checking.html
		// For testing, overapproximate and do not dispatch arguments (I understand the spec as this is whats happening,
		// but I am not sure)
		return handleUnsoundByOverapproximationWithoutDispatch(main, node, loc, name, 2,
				new CPrimitive(CPrimitives.INT));
	}

	private ExpressionResult handlePrintFunction(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc) {
		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();

		final AuxVarInfo auxvarinfo =
				mAuxVarInfoBuilder.constructAuxVarInfo(loc, new CPrimitive(CPrimitives.INT), SFO.AUXVAR.NONDET);
		resultBuilder.addDeclaration(auxvarinfo.getVarDec());
		resultBuilder.addStatement(new HavocStatement(loc, new VariableLHS[] { auxvarinfo.getLhs() }));

		final LRValue returnValue = new RValue(auxvarinfo.getExp(), new CPrimitive(CPrimitives.INT));
		resultBuilder.setLrValue(returnValue);

		// dispatch all arguments
		for (final IASTInitializerClause arg : node.getArguments()) {
			if (isStringLiteral(arg)) {
				continue;
			}
			final ExpressionResult argRes =
					mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arg);
			resultBuilder.addAllExceptLrValue(argRes);
		}

		return resultBuilder.build();
	}

	private Result handlePrintF(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc) {
		return handlePrintFunction(main, node, loc);
	}

	private Result handlePuts(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		checkArguments(loc, 1, name, node.getArguments());
		return handlePrintFunction(main, node, loc);
	}

	private boolean isStringLiteral(final IASTInitializerClause expr) {
		return expr instanceof IASTLiteralExpression
				&& ((IASTLiteralExpression) expr).getKind() == IASTLiteralExpression.lk_string_literal;
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
		final CPointer voidType = new CPointer(new CPrimitive(CPrimitives.VOID));
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
		resultBuilder.addDeclaration(auxvarinfo.getVarDec());
		resultBuilder.addAuxVar(auxvarinfo);
		resultBuilder.addStatement(call);
		resultBuilder.setLrValue(new RValue(auxvarinfo.getExp(), new CPointer(new CPrimitive(CPrimitives.VOID))));

		// add marker for global declaration to memory handler
		mMemoryHandler.requireMemoryModelFeature(mmDecl);

		// add required information to function handler.
		mProcedureManager.registerProcedure(mmDecl.getName());
		// mProcedureManager.registerCall(mmDecl.getName());

		return resultBuilder.build();
	}

	private Result handleErrorFunction(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final Expression falseLiteral = ExpressionFactory.createBooleanLiteral(loc, false);
		final Statement st = createAnnotatedAssertOrAssume(loc, name, mSettings.checkErrorFunction(),
				Spec.ERROR_FUNCTION, falseLiteral);
		return new ExpressionResult(Collections.singletonList(st), null);
	}

	/**
	 * Create an assertion or assumption statement annotated with a {@link Check} annotation.
	 *
	 * @param loc
	 *            location of the assertion or assumption node.
	 * @param functionName
	 *            name of the function for the assertion statement and {@link Check} annotation.
	 * @param checkProperty
	 *            enables creation of an assertion to check {@code expr}, otherwise an assumption is made.
	 * @param spec
	 *            type of {@link Check} for assertion or assumption statement annotation.
	 * @param expr
	 *            expression for assertion or assumption statement.
	 *
	 * @see {@link #createAnnotatedAssertOrAssume(ILocation, String, boolean, Spec, Expression, String)}
	 */
	private Statement createAnnotatedAssertOrAssume(final ILocation loc, final String functionName,
			final boolean checkProperty, final Spec spec, final Expression expr) {
		return createAnnotatedAssertOrAssume(loc, functionName, checkProperty, spec, expr, null);
	}

	/**
	 * Create an assertion or assumption statement annotated with a {@link Check} annotation.
	 *
	 * Create an {@code assert expr} or {@code assume expr} depending on the settings. If {@code checkProperty} is
	 * {@code true} (i.e. the check is enabled), an {@code assert expr} will be generated, otherwise an
	 * {@code assume expr} will be generated.
	 *
	 * @param loc
	 *            location of the assertion or assumption node.
	 * @param functionName
	 *            name of the function for the assertion statement and {@link Check} annotation.
	 * @param checkProperty
	 *            enables creation of an assertion to check {@code expr}, otherwise an assumption is made.
	 * @param spec
	 *            type of {@link Check} for assertion or assumption statement annotation.
	 * @param expr
	 *            expression for assertion or assumption statement.
	 * @param errorMsg
	 *            error message for a negative check result of an assertion.
	 *
	 * @return {@link Statement} annotated with a {@link Check} annotation.
	 */
	private Statement createAnnotatedAssertOrAssume(final ILocation loc, final String functionName,
			final boolean checkProperty, final Spec spec, final Expression expr, final String errorMsg) {
		final boolean checkMemoryleakInMain = mSettings.checkMemoryLeakInMain()
				&& mMemoryHandler.getRequiredMemoryModelFeatures().isMemoryModelInfrastructureRequired();
		if (!checkProperty && !checkMemoryleakInMain) {
			return new AssumeStatement(loc, expr);
		}

		// TODO 2017-11-26 Matthias: Workaround for memcleanup property.
		// Rationale: If we reach the SV-COMP error function (which has
		// is similar to the abort function) memory was not deallocated.
		// Proper solution: Check #valid array for all functions that
		// do not return (e.g., also abort and exit). Depending on the
		// discussion about the exact meaning of valid-memcleanup we
		// need separate arrays for stack and heap.
		// https://github.com/sosy-lab/sv-benchmarks/pull/1001
		final Check check;
		if (checkProperty) {
			final CheckMessageProvider msgProvider = new CheckMessageProvider();

			/* customize result message for error function specifications with function name */
			msgProvider.registerSpecificationErrorFunctionName(functionName);
			/* customize result message for specifications with error messages */
			msgProvider.registerSpecificationErrorMessage(spec, errorMsg);

			if (checkMemoryleakInMain) {
				check = new Check(EnumSet.of(spec, Spec.MEMORY_LEAK), msgProvider);
			} else {
				check = new Check(spec, msgProvider);
			}
		} else {
			check = new Check(EnumSet.of(Spec.MEMORY_LEAK));
		}
		final Statement st = new AssertStatement(loc, new NamedAttribute[] { new NamedAttribute(loc, "reach",
				new Expression[] { new StringLiteral(loc, check.toString()), new StringLiteral(loc, functionName) }) },
				expr);
		check.annotate(st);
		if (checkMemoryleakInMain && mSettings.isSvcompMemtrackCompatibilityMode()) {
			new Overapprox("memtrack", loc).annotate(st);
		}
		return st;
	}

	private static Result handleLtlStep(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc) {
		final NamedAttribute ltlAttribute = new NamedAttribute(loc, "ltl_step", new Expression[] {});
		final AssumeStatement assumeStmt = new AssumeStatement(loc, new NamedAttribute[] { ltlAttribute },
				ExpressionFactory.createBooleanLiteral(loc, true));
		return new ExpressionResult(Collections.singletonList(assumeStmt), null);
	}

	private Result handleByIgnore(final IDispatcher main, final ILocation loc, final String methodName) {
		mReporter.warn(loc, "ignored call to " + methodName);
		return new SkipResult();
	}

	private static Result handleByUnsupportedSyntaxException(final ILocation loc, final String functionName) {
		throw new UnsupportedSyntaxException(loc, "Unsupported function: " + functionName);
	}

	private static Result handleByUnsupportedSyntaxExceptionKnown(final ILocation loc, final String lib,
			final String functionName) {
		throw new UnsupportedSyntaxException(loc, "Unsupported function from " + lib + ": " + functionName);
	}

	/**
	 * Handle a function call by dispatching all arguments and then calling a function with no arguments that has the
	 * name of the function and is marked with the {@link Overapprox} annotation. Additionally it is assumed that the
	 * result is in range of the given type.
	 *
	 * @param main
	 *            the current dispatcher
	 * @param node
	 *            the function call expression
	 * @param loc
	 *            the location of the call
	 * @param methodName
	 *            the name of the method
	 * @param numberOfArgs
	 *            the number of arguments
	 * @param resultType
	 *            the return type
	 * @return An {@link ExpressionResult} representing the effect of the call
	 */
	private Result handleByOverapproximation(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String methodName, final int numberOfArgs, final CType resultType) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, numberOfArgs, methodName, arguments);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		for (final IASTInitializerClause argument : arguments) {
			builder.addAllExceptLrValue((ExpressionResult) main.dispatch(argument));
		}

		final ExpressionResult overapproxCall = constructOverapproximationForFunctionCall(loc, methodName, resultType);
		builder.addAllExceptLrValue(overapproxCall);
		mExpressionTranslation.addAssumeValueInRangeStatements(loc, overapproxCall.getLrValue().getValue(), resultType,
				builder);
		return builder.setLrValue(overapproxCall.getLrValue()).build();
	}

	/**
	 * We handle a function call by dispatching all arguments, but we then ignore the call completely.
	 *
	 * Useful for void functions that do nothing.
	 */
	private static Result handleVoidFunctionBySkipAndDispatch(final IDispatcher main,
			final IASTFunctionCallExpression node, final ILocation loc, final String methodName,
			final int numberOfArgs) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, numberOfArgs, methodName, arguments);
		final List<ExpressionResult> results = new ArrayList<>();
		for (final IASTInitializerClause argument : arguments) {
			results.add((ExpressionResult) main.dispatch(argument));
		}
		return new ExpressionResultBuilder().addAllExceptLrValue(results).build();
	}

	/**
	 * Overapproximate the reachability of unsupported functions by translating them to while(true) assert false; where
	 * the assert is labeled with an overapproximation
	 */
	private Result handleUnsupportedFunctionByOverapproximation(final IDispatcher main, final ILocation loc,
			final String name, final CType returnType) {
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final Statement unreach = new AssertStatement(loc, ExpressionFactory.createBooleanLiteral(loc, false));
		new Overapprox(name, loc).annotate(unreach);
		new Check(Spec.UNKNOWN).annotate(unreach);
		builder.addStatement(new WhileStatement(loc, ExpressionFactory.createBooleanLiteral(loc, true),
				new LoopInvariantSpecification[0], new Statement[] { unreach }));
		if (!returnType.isVoidType()) {
			final AuxVarInfo auxVar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, returnType, AUXVAR.NONDET);
			builder.addAuxVar(auxVar).addDeclaration(auxVar.getVarDec());
			builder.setLrValue(new RValue(auxVar.getExp(), returnType));
		}
		return builder.build();
	}

	private Result handleUnsoundByOverapproximationWithoutDispatch(final IDispatcher main,
			final IASTFunctionCallExpression node, final ILocation loc, final String methodName, final int numberOfArgs,
			final CType resultType) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, numberOfArgs, methodName, arguments);
		return constructOverapproximationForFunctionCall(loc, methodName, resultType);
	}

	/**
	 * Construct an auxiliary variable that will be use as a substitute for a function call. The result will be marked
	 * as an overapproximation. If you overapproximate a function call, don't forget to dispatch the function call's
	 * arguments: the arguments may have side effects.
	 *
	 * @param functionName
	 *            the named of the function will be annotated to the overapproximation
	 * @param resultType
	 *            CType that determinies the type of the auxiliary variable
	 */
	private ExpressionResult constructOverapproximationForFunctionCall(final ILocation loc, final String functionName,
			final CType resultType) {
		return buildFunctionCall(loc, resultType).addOverapprox(new Overapprox(functionName, loc)).build();
	}

	private ExpressionResult handleByFunctionCall(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name, final CType resultType) {
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final IASTInitializerClause[] arguments = node.getArguments();
		final Expression[] translatedArgs = new Expression[arguments.length];
		for (int i = 0; i < arguments.length; i++) {
			final ExpressionResult dispatched = (ExpressionResult) main.dispatch(arguments[i]);
			builder.addAllExceptLrValue(dispatched);
			translatedArgs[i] = dispatched.getLrValue().getValue();
		}
		VariableLHS[] retValue;
		if (resultType.isVoidType()) {
			retValue = new VariableLHS[0];
		} else {
			final AuxVarInfo auxVar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, resultType, AUXVAR.RETURNED);
			builder.addAuxVar(auxVar).addDeclaration(auxVar.getVarDec());
			retValue = new VariableLHS[] { auxVar.getLhs() };
		}
		builder.addStatement(StatementFactory.constructCallStatement(loc, false, retValue, name, translatedArgs));
		return builder.build();
	}

	private ExpressionResultBuilder buildFunctionCall(final ILocation loc, final CType resultType) {
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final AuxVarInfo auxvar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, resultType, SFO.AUXVAR.NONDET);
		builder.addDeclaration(auxvar.getVarDec());
		builder.addAuxVar(auxvar);
		builder.setLrValue(new RValue(auxvar.getExp(), resultType));
		return builder;
	}

	private static void checkArguments(final ILocation loc, final int expectedArgs, final String name,
			final IASTInitializerClause[] arguments) {
		if (arguments.length != expectedArgs) {
			throw new IncorrectSyntaxException(loc, name + " is expected to have " + expectedArgs
					+ " arguments, but was called with " + arguments.length);
		}
	}

	private static <K, V> void fill(final Map<K, V> map, final K key, final V value) {
		final V old = map.put(key, value);
		if (old != null) {
			throw new AssertionError("Accidentally overwrote definition for " + key);
		}
	}

	/**
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 */
	@FunctionalInterface
	private interface IFunctionModelHandler {
		Result handleFunction(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
				String methodName);
	}
}
