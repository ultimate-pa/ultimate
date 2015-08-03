/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2;

import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.apache.log4j.Logger;

import sun.reflect.generics.reflectiveObjects.NotImplementedException;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.*;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.*;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.*;

/**
 * Used to evaluate boogie statements during abstract interpretation
 * 
 * @author GROSS-JAN
 */
public class AIVisitor implements IRCFGVisitor, IStatementVisitor
{
	private static StatementWalker sStatementWalker = new StatementWalker();

	private final IUltimateServiceProvider mServices;
	private final Logger mLogger;
	private final BoogieSymbolTable mSymbolTable;
	private final IAbstractDomain mDomain;

	/**
	 * Where we are at the moment, and where to put the resulting state
	 */
	private RCFGNode mCurrentNode;

	/**
	 * After visiting each code block, the resulting state is in mResulting
	 * state It will be merged into mMergedState. So in case we are in a
	 * parallel sequence the merged state can be extracted from there
	 */
	private StackState mCurrentState;

	/**
	 * After visiting each code block, the resulting state is in mResulting
	 * state It will be merged into mMergedState. So in case we are in a
	 * parallel sequence the merged state can be extracted from there
	 */
	private StackState mResultingState;
	/**
	 * Holds a list with a sequence element for each sequential code block which
	 * was entered and information about its paralellity
	 */
	private LinkedList<AIVisitorStackElement> mCompositions = new LinkedList<AIVisitorStackElement>();

	private DeclarationInformation mDeclarationInformation;

	/**
	 * Can be set to false to interrupt processing
	 */
	private boolean mContinueProcessing;

	/**
	 * Numbers which shall be used for widening.
	 */
	private final Set<String> mNumbersForWidening;

	/**
	 * If the visitor encounters any errors (like unsupported syntax), an error
	 * message is written to this variable. The AbstractInterpreter checks for
	 * such messages and returns an appropriate result.
	 */
	private String mError = "";

	private boolean mViolatedAssert;
	private String mResult;

	public boolean getContinueProcessing()
	{
		return mContinueProcessing;
	}

	public void setCurrentState(StackState state)
	{
		mCurrentState = state;
	}

	public void setCurrentNode(RCFGNode node)
	{
		mCurrentNode = node;
	}

	public StackState getResultingState()
	{
		return mResultingState;
	}

	public String getError()
	{
		return mError;
	}

	public boolean violatedAssert()
	{
		return mViolatedAssert;
	}

	public String getResult()
	{
		return mResult;
	}

	/**
	 * Constructor
	 * 
	 * 
	 * @param logger
	 * @param services
	 * @param symbolTable
	 * @param domain
	 * @param numbersForWidening
	 */
	public AIVisitor(
			Logger logger,
			IUltimateServiceProvider services,
			BoogieSymbolTable symbolTable,
			IAbstractDomain<?> domain,
			Set<String> numbersForWidening)
	{
		mLogger = logger;
		mServices = services;
		mSymbolTable = symbolTable;
		mDomain = domain;
		mNumbersForWidening = numbersForWidening;
		mResult = null;
		mViolatedAssert = false;
		mContinueProcessing = true;
	}

	public void prepare()
	{
		mCompositions.clear();
	}


	/**
	 * After visiting each edge, the resulting state is in mMergedState
	 */
	@Override
	public void visitEdge(RCFGEdge e)
	{
		mLogger.debug("Visiting: " + e.getSource() + " -> " + e.getTarget());

		mResultingState = null;
		mCompositions.push(new AIVisitorStackElement(false));

		//mResultingState = 
		mContinueProcessing = true;
	}

	@Override
	public void visitedEdge(RCFGEdge e)
	{
		if (!mError.isEmpty())
		{
			mResultingState = null; // return, abort, stop.
		}
	}

	/**
	 * After visiting each code block, the resulting state is in mResulting
	 * state It will be merged into mMergedState. So in case we are in a
	 * parallel sequence the merged state can be extracted from there
	 */
	@Override
	public void visitCodeBlock(CodeBlock c)
	{
		mLogger.debug("> CodeBlock START");

		// if there is an intermediate result, take it
		// as a starting point
		if (mResultingState != null)
		{
			mCurrentState = mResultingState;
			mResultingState = null;
		}
	}

	@Override
	public void visitedCodeBlock(CodeBlock c)
	{
		// if processing in parallel merge the resulting
		// state into the merge-state

		AIVisitorStackElement seq = mCompositions.peek();
		if (seq.getProcessInParalell() && mResultingState != null)
		{
			if (seq.getState() == null)
			{
				seq.setState(mResultingState);
			}
			else
			{
				seq.setState(mResultingState.merge(seq.getState(), false));
			}
			mResultingState = null;
		}

		mLogger.debug("< CodeBlock END");
	}

	/**
	 * After visiting each edge, the resulting state is in mResulting state
	 * which gets merged to mMergedState
	 */
	@Override
	public void visit(ParallelComposition c)
	{
		mLogger.debug("> ParallelComposition START");
		mCompositions.push(new AIVisitorStackElement(true));
	}

	/**
	 * After visiting each edge, the resulting state is in mResulting state
	 * which gets merged to mMergedState. Now we take that merged state, as it
	 * is the resulting state of the parallel composition
	 */
	@Override
	public void visited(ParallelComposition c)
	{
		AIVisitorStackElement seq = mCompositions.pop();
		mResultingState = seq.getState();
		mLogger.debug("< ParallelComposition END");
	}

	@Override
	public void visit(SequentialComposition c)
	{
		mLogger.debug("> SequentialComposition START");
		mCompositions.push(new AIVisitorStackElement(false));
	}

	@Override
	public void visited(SequentialComposition c)
	{
		AIVisitorStackElement seq = mCompositions.pop();
		mResultingState = seq.getState();
		mLogger.debug("< SequentialComposition END");
	}

	@Override
	public void visit(RootEdge c)
	{
		mLogger.debug("> RootEdge");
		throw new NotImplementedException();
	}

	@Override
	public void visit(GotoEdge c)
	{
		mLogger.debug("> GotoEdge (copy)");
		mResultingState = mCurrentState.copy();
	}

	@Override
	public void visit(Call c)
	{
		CallStatement stmt = c.getCallStatement();

		throw new NotImplementedException();
	}

	@Override
	public void visit(Return c)
	{
		throw new NotImplementedException();
	}

	@Override
	public void visit(StatementSequence c)
	{
		mLogger.debug("> StatementSequence START");
		//mCompositions.push(new AIVisitorStackElement(false));
	}

	@Override
	public void visited(StatementSequence c)
	{
		//AIVisitorStackElement seq = mCompositions.pop();
		//mResultingState = seq.getState();
		mLogger.debug("< StatementSequence END");
	}

	@Override
	public void visit(Summary c)
	{
		// TODO Auto-generated method stub
		throw new NotImplementedException();
	}

	@Override
	public void visited(Summary c)
	{
		// TODO Auto-generated method stub
		throw new NotImplementedException();
	}

	@Override
	public void visitStatement(Statement e)
	{
		mLogger.debug("> Statement START");
	}

	@Override
	public void visitedStatement(Statement e)
	{
		if(mCompositions.peek().getProcessInParalell())
		{
			throw new NotImplementedException();
		}
		mLogger.debug("< Statement END");
	}

	@Override
	public void visit(AssertStatement s)
	{
		mLogger.debug("Applying assert: " + s.toString());
		if (!mDomain.ApplyAssert(mCurrentState.getCurrentScope().getState(), s.getFormula()))
		{
			mViolatedAssert = false;
			mResult = "assert was not fulfilled: " + s.getFormula();
			mResultingState = null;			
		}

		// mResultingState = mCurrentState.increment(resultingState);
	}

	@Override
	public void visit(AssignmentStatement s)
	{
		// apply the formula on a copy of the topmost state
		IAbstractState resultingState = mCurrentState.getCurrentScope().getState().copy();
		
		LeftHandSide[] lhs = s.getLhs();
		Expression[] rhs = s.getRhs();
		
		if (lhs.length != rhs.length) 
		{
			mLogger.warn(String.format("%s lhs and rhs size mismatch!", s.getClass()));
			return;
		}
		assert (s.getLhs().length == s.getRhs().length);
		
		for (int i = 0; i < s.getLhs().length; i++)
		{
			LeftHandSide l = lhs[i];
			Expression r = rhs[i];
			AbstractVariable variable;
			if (l instanceof ArrayLHS)
			{
				throw new NotImplementedException();
			}
			else if (l instanceof VariableLHS)
			{
				VariableLHS var = (VariableLHS) l;
				variable = new AbstractVariable(var.getIdentifier(), null);
			}
			else
			{
				throw new UnsupportedOperationException(String.format("Unsupported LeftHandSide type %s", l.getClass()));
			}
			resultingState = mDomain.ApplyExpression(resultingState, variable, l.getType(), r);
		}

		mResultingState = mCurrentState.increment(resultingState);
	}

	@Override
	public void visit(AssumeStatement s)
	{
		// apply the formula on a copy of the topmost state
		IAbstractState resultingState = mCurrentState.getCurrentScope().getState().copy();
		resultingState = mDomain.ApplyAssume(resultingState, s.getFormula());

		// set the result to a copy of the state
		mResultingState = mCurrentState.increment(resultingState);
	}

	@Override
	public void visit(HavocStatement s)
	{
		// apply the formula on a copy of the topmost state
		IAbstractState resultingState = mCurrentState.getCurrentScope().getState().copy();

		for (VariableLHS lhs : s.getIdentifiers())
		{
			mLogger.debug("Havoc : " + lhs.getIdentifier());

			AbstractVariable variable = new AbstractVariable(lhs.getIdentifier(), null);
			resultingState = mDomain.ApplyHavoc(resultingState, variable, lhs.getType());
		}

		// set the result to a copy of the state
		mResultingState = mCurrentState.increment(resultingState);
	}

	@Override
	public void visit(BreakStatement s)
	{
		throw new NotImplementedException();
	}

	@Override
	public void visit(CallStatement s)
	{
		// add a new scope (copies the actual)
		mCurrentState.pushStackLayer(s);

		// arguments of the call
		Expression[] arguments = s.getArguments();
		
		// fetch method declaration to get input parameters
		List<Declaration> methodDecList = mSymbolTable.getFunctionOrProcedureDeclaration(s.getMethodName());

		if (methodDecList.size() >= 1)
		{
			Declaration methodDec = methodDecList.get(0);
			VarList[] parameters = null;
			if (methodDec instanceof FunctionDeclaration)
			{
				FunctionDeclaration functionDec = (FunctionDeclaration) methodDec;
				parameters = functionDec.getInParams();
			}
			else if (methodDec instanceof Procedure)
			{
				Procedure procedureDec = (Procedure) methodDec;
				parameters = procedureDec.getInParams();
			}
			else
			{
				mLogger.warn(String.format("Unknown method declaration kind \"%s\" encountered.", methodDec));
			}
			
			if (parameters == null)
			{
				return;
			}
			
			// apply the expression on the local variables in the new state
			int currentExpression = 0;
			for (int p = 0; p < parameters.length; p++)
			{
				// for each type of parameter there may be several identifiers
				String[] identifiers = parameters[p].getIdentifiers();
				IType type = parameters[p].getType().getBoogieType();
				for (int i = 0; i < identifiers.length; i++)
				{
					if(currentExpression >= arguments.length)
					{
						// this may not happen
						String err = String.format("Invalid number of arguments for method call of \"%s\"", s.getMethodName());
						mLogger.error(err);
						mError = err;					
						return;
					}
					// match it to the expression
					Expression expression = arguments[currentExpression++];
				
					mCurrentState.increment(mDomain.ApplyExpression(
						mCurrentState.getCurrentState(),
						new AbstractVariable(identifiers[i], null),
						type,
						expression));
				}					
			}
		}
	}

	@Override
	public void visit(GotoStatement s)
	{
		throw new NotImplementedException();
	}

	@Override
	public void visit(IfStatement s)
	{
		throw new NotImplementedException();
	}

	@Override
	public void visit(Label s)
	{
		mLogger.debug("Label : " + s.getName());
	}

	@Override
	public void visit(ReturnStatement s)
	{
		throw new NotImplementedException();
	}

	@Override
	public void visit(WhileStatement s)
	{
		throw new NotImplementedException();
	}

	@Override
	public IStatementVisitor getStatementVisitor()
	{
		return this;
	}

	@Override
	public StatementWalker getStatementWalker()
	{
		return sStatementWalker;
	}
}
