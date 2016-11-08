/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE RCFGBuilder plug-in.
 * 
 * The ULTIMATE RCFGBuilder plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE RCFGBuilder plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE RCFGBuilder plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE RCFGBuilder plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE RCFGBuilder plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;

/**
 * Edge in a recursive control flow graph that represents a sequence of
 * statements which are executed one after the other if this edge is executed.
 * The name of this objects Payload is
 * <ul>
 * <li>a prettyprinted representation of the Statements, if the origin of this
 * edge is the implementation,</li>
 * <li>"Assert" if origin of this edge is an AssertStatement,</li>
 * <li>"Requires" if origin of this edge is the requires specification,</li>
 * <li>"Ensures" if origin of this edge is the ensures specification.</li>
 * </ul>
 * 
 * @author heizmann@informatik.uni-freiburg.de
 */
public class StatementSequence extends CodeBlock implements IInternalAction {

	private static final long serialVersionUID = -1780068525981157749L;

	public static enum Origin {
		ENSURES, REQUIRES, IMPLEMENTATION, ASSERT
	};

	private final List<Statement> mStatements = new ArrayList<Statement>();
	private String mPrettyPrintedStatements = "";
	/**
	 * mOrigin stores the origin of this InternalEdge, which could be either be
	 * the ensures specification, the requires specification or the
	 * implementation of a program.
	 */
	private final Origin mOrigin;

	/**
	 * The published attributes. Update this and getFieldValue() if you add new
	 * attributes.
	 */
	private final static String[] s_AttribFields = { "Statements", "PrettyPrintedStatements", "TransitionFormula",
			"OccurenceInCounterexamples" };

	StatementSequence(int serialNumber, BoogieIcfgLocation source, BoogieIcfgLocation target, Statement st, ILogger logger) {
		super(serialNumber, source, target, logger);
		mOrigin = Origin.IMPLEMENTATION;
		addStatement(st);
	}

	StatementSequence(int serialNumber, BoogieIcfgLocation source, BoogieIcfgLocation target, Statement st, Origin origin, ILogger logger) {
		super(serialNumber, source, target, logger);
		mOrigin = origin;
		addStatement(st);
	}

	StatementSequence(int serialNumber, BoogieIcfgLocation source, BoogieIcfgLocation target, List<Statement> stmts, Origin origin,
			ILogger logger) {
		super(serialNumber, source, target, logger);
		mStatements.addAll(stmts);
		mOrigin = origin;
		mPrettyPrintedStatements = "";
		for (final Statement st : stmts) {
			mPrettyPrintedStatements += BoogiePrettyPrinter.print(st);
		}
	}
	
	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "Statements") {
			return mStatements;
		} else if (field == "PrettyPrintedStatements") {
			return mPrettyPrintedStatements;
		} else if (field == "TransitionFormula") {
			return mTransitionFormula;
		} else if (field == "OccurenceInCounterexamples") {
			return mOccurenceInCounterexamples;
		} else {
			throw new UnsupportedOperationException("Unknown field " + field);
		}
	}

	public void addStatement(Statement st) {
		if (st instanceof AssumeStatement || st instanceof AssignmentStatement || st instanceof HavocStatement) {
		} else {
			throw new IllegalArgumentException("Only Assignment, Assume and"
					+ " HavocStatement allowed in InternalEdge.");
		}
		mStatements.add(st);
		mPrettyPrintedStatements += BoogiePrettyPrinter.print(st);
	}

	public List<Statement> getStatements() {
		return mStatements;
	}

	@Override
	public String getPrettyPrintedStatements() {
		return mPrettyPrintedStatements;
	}

	public Origin getOrigin() {
		return mOrigin;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		for (final Statement st : mStatements) {
			sb.append(BoogiePrettyPrinter.print(st));
		}
		return sb.toString();
	}

	@Override
	public UnmodifiableTransFormula getTransformula() {
		return getTransitionFormula();
	}

}
