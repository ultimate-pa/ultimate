package de.uni_freiburg.informatik.ultimate.buchiprogramproduct.optimizeproduct;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;


/**
 *
 * TODO 
 * YVTransformation
 * 
 * Zweck: Zustände minimieren. 
 *  
 * Einfaches Beispiel: 
 * - q3 hat genau drei Kanten (q1, st1, q3), (q2, st2, q3), (q3, st3, q4)
 * - q1 und q2 akzeptierend oder q3 nicht akzeptierend oder q4 akzeptierend
 * - Ersetze die drei Kanten durch (q1, st1;st3 q4) und (q2 st2;st3 q4)
 * 
 * Symmetrischer Fall: YV auf dem Kopf
 * Erweiterung: Beliebig viele eingehende und ausgehende Kanten für q3
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class MinimizeStatesWithYVTransformation extends BaseProductOptimizer {

	public MinimizeStatesWithYVTransformation(RootNode product, IUltimateServiceProvider services) {
		super(product, services);
		// TODO Auto-generated constructor stub
	}

	@Override
	protected void init(RootNode root, IUltimateServiceProvider services) {
		// TODO Auto-generated method stub

	}

	@Override
	protected RootNode process(RootNode root) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean IsGraphChanged() {
		// TODO Auto-generated method stub
		return false;
	}

}
