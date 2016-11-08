/*
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE SpaceExParser plug-in.
 * 
 * The ULTIMATE SpaceExParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE SpaceExParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SpaceExParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SpaceExParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE SpaceExParser plug-in grant you additional permission 
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.spaceex.test;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Marshaller;
import javax.xml.bind.Unmarshaller;

import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.HybridModel;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.SpaceExModelBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.ObjectFactory;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.Sspaceex;
import de.uni_freiburg.informatik.ultimate.test.ConsoleLogger;

/**
 * Parser test and construction test class.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class Tester {

	public static void main(String[] args) throws JAXBException, IOException {

		final JAXBContext jc = JAXBContext.newInstance(ObjectFactory.class);

		final Unmarshaller unmarshaller = jc.createUnmarshaller();

		final String testfile = "<?xml version=\"1.0\" encoding=\"iso-8859-1\"?>\n"
		        + "<sspaceex xmlns=\"http://www-verimag.imag.fr/xml-namespaces/sspaceex\" version=\"0.2\" math=\"SpaceEx\">"
		        + "<component id=\"aut1\">"
		        + "<param name=\"x\" type=\"real\" local=\"false\" d1=\"1\" d2=\"1\" dynamics=\"any\" />"
		        + "<location id=\"1\" name=\"loc1\" x=\"316.0\" y=\"129.0\" width=\"108.0\" height=\"76.0\">"
		        + "<invariant>0 &lt;= x &lt;= 10</invariant>" + "<flow>x'==1</flow>" + "</location>" + "</component>"
		        + "<component id=\"sys1\">" + "<bind component=\"aut1\" as=\"aut1_1\" x=\"200.0\" y=\"129.0\">"
		        + "<map key=\"x\">x</map>" + "</bind>" + "</component>" + "</sspaceex>";
		final File f = new File("../../examples/programs/spaceex/bball.xml");

		FileInputStream fis = null;

		InputStream is;
		if (f.exists()) {
			fis = new FileInputStream(f);
			is = fis;
		} else {
			System.out.println("File does not exist: " + f.getPath());
			is = new ByteArrayInputStream(testfile.getBytes());
		}

		final Sspaceex sx = (Sspaceex) unmarshaller.unmarshal(is);

		final HybridModel hs = new HybridModel(sx, new ConsoleLogger());
		
		final SpaceExModelBuilder modelBuilder = new SpaceExModelBuilder(hs, new ConsoleLogger());
		
		final Marshaller marshaller = jc.createMarshaller();

		marshaller.setProperty(Marshaller.JAXB_FORMATTED_OUTPUT, Boolean.TRUE);

		final FileOutputStream fos = new FileOutputStream(new File("/tmp/output.xml"));

		marshaller.marshal(sx, System.out);
		marshaller.marshal(sx, fos);

		fos.close();
		if (fis != null) {
			fis.close();
		}
	}

}
