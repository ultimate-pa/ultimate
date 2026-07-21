/*
 * Copyright (C) 2026 Matthias Zumkeller
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE BoogiePreprocessor plug-in.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogiePreprocessor plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogiePreprocessor plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BoogiePreprocessor plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.preprocessor;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.InterruptAnnotation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.InterruptAnnotation.ISRLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.InterruptRequest;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.function.InterruptServiceFunction;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;

/**
 * Visit all procedures of a Boogie unit and add interrupt annotations (see {@link InterruptAnnotation}) to all
 * statements between two enclosing labels that mark an ISR.
 */
public class InterruptAnnotator extends BoogieVisitor implements IUnmanagedObserver {

	private VisitorContext mContext = new VisitorContext(VisitorMode.NORMAL, null);

	@Override
	/**
	 * Visit each procedure of the Boogie program and annotate the statements belonging to some ISR
	 */
	public boolean process(final IElement root) throws Throwable {
		if (root instanceof final Unit unit) {
			for (final Declaration decl : unit.getDeclarations()) {
				if (decl instanceof final Procedure proc) {
					visit(proc);
				}
			}
			return false;
		}
		return true;
	}

	@Override
	protected void visit(final Procedure procedure) {
		final var body = procedure.getBody();
		if (body == null) {
			return;
		}
		processStatements(body.getBlock());
	}

	@Override
	protected Statement processStatement(final Statement statement) {
		addAnnotationIfInContext(statement);
		return super.processStatement(statement);
	}

	@Override
	protected void visit(final Label statement) {
		if (mContext.visitorMode == VisitorMode.NORMAL) {
			if (!isISRLabel(statement, "entry")) {
				assert !isISRLabel(statement, "exit");
				return;
			}
			final var newInterruptAnno = new InterruptAnnotation(ISRLocation.ISR, getIsr(statement));
			mContext = new VisitorContext(VisitorMode.ISR_INNER, newInterruptAnno);
		} else {
			if (!isISRLabel(statement, "exit")) {
				assert !isISRLabel(statement, "entry");
				return;
			}
			mContext = new VisitorContext(VisitorMode.NORMAL, null);
		}
		super.visit(statement);
	}

	private void addAnnotationIfInContext(final Statement statement) {
		if (mContext.visitorMode == VisitorMode.NORMAL) {
			return;
		} else if (InterruptAnnotation.hasAnnotation(statement)) {
			return;
		}
		mContext.currentAnnotation.annotate(statement);
	}

	private static boolean isISRLabel(final Label label, final String isrLabelPosition) {
		final var attributes = label.getAttributes();
		if (attributes == null || attributes.length != 3) {
			return false;
		}
		final var attributeName = attributes[0].getName();
		final var positionAttribute = attributes[1].getName();
		return attributeName.equals("isr_label") && positionAttribute.equals(isrLabelPosition);
	}

	private static InterruptServiceFunction getIsr(final Label label) {
		final NamedAttribute[] attributes = label.getAttributes();
		final String irqNameStr = attributes[2].getName();
		final String irqNumStr = attributes[4].getName();
		return new InterruptServiceFunction(new InterruptRequest(irqNameStr, Integer.parseInt(irqNumStr)));
	}

	private enum VisitorMode {
		NORMAL, ISR_INNER
	}

	/**
	 * Record that stores state information about the visitor. More precisely it stores whether the currently visited
	 * node is part of an ISR and also the corresponding InterruptAnnotation
	 */
	private record VisitorContext(VisitorMode visitorMode, InterruptAnnotation currentAnnotation) {
	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels)
			throws Throwable {
		// TODO Auto-generated method stub

	}

	@Override
	public void finish() throws Throwable {
		// TODO Auto-generated method stub

	}

	@Override
	public boolean performedChanges() {
		// TODO Auto-generated method stub
		return false;
	}
}
