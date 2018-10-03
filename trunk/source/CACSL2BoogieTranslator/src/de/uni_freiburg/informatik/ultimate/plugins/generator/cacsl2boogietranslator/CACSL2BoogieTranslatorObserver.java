/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
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
/**
 * The plug-in's Observer
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.cdt.decorator.ASTDecorator;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.MainTranslator;
import de.uni_freiburg.informatik.ultimate.core.lib.models.WrapperNode;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.witness.CorrectnessWitnessExtractor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.witness.ExtractedWitnessInvariant;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessGraphAnnotation;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 */
public class CACSL2BoogieTranslatorObserver implements IUnmanagedObserver {

	private final ILogger mLogger;
	private final IToolchainStorage mStorage;
	private final IUltimateServiceProvider mServices;
	private final ACSLObjectContainerObserver mAdditionalAnnotationObserver;
	private final CorrectnessWitnessExtractor mWitnessExtractor;

	private WrapperNode mRootNode;
	private ASTDecorator mInputDecorator;
	private boolean mLastModel;
	private Map<IASTNode, ExtractedWitnessInvariant> mWitnessInvariants;

	public CACSL2BoogieTranslatorObserver(final IUltimateServiceProvider services, final IToolchainStorage storage,
			final ACSLObjectContainerObserver additionalAnnotationObserver) {
		assert storage != null;
		assert services != null;
		mStorage = storage;
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mWitnessExtractor = new CorrectnessWitnessExtractor(mServices);
		mAdditionalAnnotationObserver = additionalAnnotationObserver;
	}

	@Override
	public boolean process(final IElement root) {
		if (root instanceof WitnessNode) {
			extractWitnessInformation((WitnessNode) root);
			return false;
		}

		if ((root instanceof WrapperNode) && (((WrapperNode) root).getBacking() instanceof ASTDecorator)) {
			mInputDecorator = (ASTDecorator) ((WrapperNode) root).getBacking();
			if (mInputDecorator.countUnits() == 1) {
				mWitnessExtractor.setAST(mInputDecorator.getUnit(0).getSourceTranslationUnit());
			} else {
				mLogger.info("Witness extractor is disabled for multiple files");
			}
			return false;
		}

		if (root instanceof Unit) {
			throw new UnsupportedOperationException(
					"Your input file is a Boogie program. This plugin takes as input a C program.");
		}
		return false;
	}

	private void extractWitnessInformation(final WitnessNode wnode) {
		final WitnessGraphAnnotation graphAnnot = WitnessGraphAnnotation.getAnnotation(wnode);

		switch (graphAnnot.getWitnessType()) {
		case VIOLATION_WITNESS:
			// is currently not handled here. May happen in the future if we want to handle assume
			break;
		case CORRECTNESS_WITNESS:
			mWitnessExtractor.setWitness(wnode);
			break;
		default:
			throw new UnsupportedOperationException("Unknown witness type " + graphAnnot.getWitnessType());
		}
	}

	@Override
	public void finish() {
		if (mWitnessExtractor.isReady()) {
			mWitnessInvariants = mWitnessExtractor.getCorrectnessWitnessInvariants();
		}
		if (mLastModel) {
			mRootNode = new MainTranslator(mServices, mStorage, mLogger, mWitnessInvariants, mInputDecorator.getUnits(),
					mInputDecorator.getSymbolTable(), mAdditionalAnnotationObserver.getAnnotation()).getResult();
		}
	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels) {
		if (currentModelIndex == numberOfModels - 1) {
			mLastModel = true;
		}
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

	public IElement getRoot() {
		return mRootNode;
	}
}
