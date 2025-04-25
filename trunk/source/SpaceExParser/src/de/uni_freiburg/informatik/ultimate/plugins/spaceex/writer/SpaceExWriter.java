package de.uni_freiburg.informatik.ultimate.plugins.spaceex.writer;

import java.io.File;
import java.io.FileOutputStream;
import java.io.StringWriter;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.HybridAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.Location;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.Transition;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.ComponentType;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.LocationType;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.ObjectFactory;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.ParamType;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.Sspaceex;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.TransitionType;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.TransitionType.Labelposition;
import jakarta.xml.bind.JAXBContext;
import jakarta.xml.bind.Marshaller;

/**
 * Class that provides functions to convert {@link HybridAutomaton} to {@link Sspaceex} and write them to disk
 *
 * @author Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 */
public class SpaceExWriter {
	ILogger mLogger;

	public SpaceExWriter(final ILogger logger) {
		mLogger = logger;
	}

	/**
	 * Function that converts {@link HybridAutomaton} to {@link Sspaceex}
	 *
	 * @param automaton
	 * @return
	 */
	public Sspaceex HybridAutomatonToSpaceEx(final HybridAutomaton automaton) {
		// TODO: functions for all this stuff
		double x = 100;
		final Sspaceex root = new Sspaceex();
		final Map<Integer, Location> locations = automaton.getLocations();
		final List<Transition> transitions = automaton.getTransitions();
		final Set<String> locParams = automaton.getLocalParameters();
		final Set<String> globParams = automaton.getGlobalParameters();
		final Set<String> locConsts = automaton.getLocalConstants();
		final Set<String> globConsts = automaton.getGlobalConstants();
		final Set<String> labels = automaton.getLabels();
		// create component
		final ComponentType comp = new ComponentType();
		comp.setId("aut1");
		// create LocationTypes
		for (final Location location : locations.values()) {
			final LocationType loc = new LocationType();
			loc.setId(location.getId());
			loc.setName(location.getName());
			loc.setFlow(location.getFlow());
			loc.setInvariant(location.getInvariant());
			loc.setHeight(100.0);
			loc.setWidth(100.0);
			loc.setX(x);
			loc.setY(100.0);
			comp.getLocation().add(loc);
			x += 100;
		}
		// create TransitionTypes
		for (final Transition transition : transitions) {
			final TransitionType trans = new TransitionType();
			trans.setSource(transition.getSourceId());
			trans.setTarget(transition.getTargetId());
			if (transition.getUpdate() != "") {
				trans.setAssignment(transition.getUpdate());
			}
			if (transition.getGuard() != "") {
				trans.setGuard(transition.getGuard());
			}
			if (transition.getLabel() != "") {
				trans.setLabel(transition.getLabel());
			}
			final Labelposition labpos = new Labelposition();
			labpos.setX(0.0);
			labpos.setY(0.0);
			trans.setLabelposition(labpos);
			comp.getTransition().add(trans);
		}
		// create ParamTypes
		for (final String parameter : locParams) {
			final ParamType param = new ParamType();
			param.setName(parameter);
			param.setLocal(true);
			param.setType("real");
			param.setDynamics("any");
			param.setD1(1);
			param.setD2(1);
			param.setControlled(true);
			comp.getParam().add(param);
		}
		for (final String parameter : globParams) {
			final ParamType param = new ParamType();
			param.setName(parameter);
			param.setLocal(false);
			param.setType("real");
			param.setDynamics("any");
			param.setD1(1);
			param.setD2(1);
			param.setControlled(true);
			comp.getParam().add(param);
		}
		for (final String parameter : locConsts) {
			final ParamType param = new ParamType();
			param.setName(parameter);
			param.setLocal(true);
			param.setType("real");
			param.setDynamics("const");
			param.setD1(1);
			param.setD2(1);
			param.setControlled(true);
			comp.getParam().add(param);
		}
		for (final String parameter : globConsts) {
			final ParamType param = new ParamType();
			param.setName(parameter);
			param.setLocal(false);
			param.setType("real");
			param.setDynamics("const");
			param.setD1(1);
			param.setD2(1);
			param.setControlled(true);
			comp.getParam().add(param);
		}
		for (final String parameter : labels) {
			final ParamType param = new ParamType();
			param.setName(parameter);
			param.setLocal(false);
			param.setType("label");
			comp.getParam().add(param);
		}
		root.getComponent().add(comp);
		return root;
	}

	/**
	 * Function that writes a given {@link Sspaceex} root to disk
	 *
	 * @param root
	 * @param targetfile
	 * @throws Exception
	 */
	public void writeXmlToDisk(final Sspaceex root, final String targetfile) throws Exception {
		final JAXBContext jaxContext = JAXBContext.newInstance(ObjectFactory.class);
		final Marshaller marshaller = jaxContext.createMarshaller();
		final StringWriter streamWriter = new StringWriter();
		marshaller.setProperty(Marshaller.JAXB_FORMATTED_OUTPUT, Boolean.TRUE);
		final FileOutputStream fos = new FileOutputStream(new File(targetfile));
		marshaller.marshal(root, fos);
		marshaller.marshal(root, streamWriter);
		mLogger.info(streamWriter.toString());
		fos.close();
	}

}
