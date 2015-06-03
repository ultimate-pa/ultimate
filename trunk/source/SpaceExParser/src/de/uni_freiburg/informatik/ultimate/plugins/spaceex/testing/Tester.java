package de.uni_freiburg.informatik.ultimate.plugins.spaceex.testing;

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

import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.*;

//import fr.imag.www_verimag.xml_namespaces.sspaceex.ObjectFactory;
//import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.*;
//import fr.imag.www_verimag.xml_namespaces.sspaceex.Sspaceex;

public class Tester {

	public static void main(String[] args) throws JAXBException, IOException {

		JAXBContext jc = JAXBContext.newInstance(ObjectFactory.class);

		Unmarshaller unmarshaller = jc.createUnmarshaller();

		String testfile = "<?xml version=\"1.0\" encoding=\"iso-8859-1\"?>\n"
				+ "<sspaceex xmlns=\"http://www-verimag.imag.fr/xml-namespaces/sspaceex\" version=\"0.2\" math=\"SpaceEx\">"
				+ "<component id=\"aut1\">"
				+ "<param name=\"x\" type=\"real\" local=\"false\" d1=\"1\" d2=\"1\" dynamics=\"any\" />"
				+ "<location id=\"1\" name=\"loc1\" x=\"316.0\" y=\"129.0\" width=\"108.0\" height=\"76.0\">"
				+ "<invariant>0 &lt;= x &lt;= 10</invariant>"
				+ "<flow>x'==1</flow>"
				+ "</location>"
				+ "</component>"
				+ "<component id=\"sys1\">"
				+ "<bind component=\"aut1\" as=\"aut1_1\" x=\"200.0\" y=\"129.0\">"
				+ "<map key=\"x\">x</map>"
				+ "</bind>"
				+ "</component>"
				+ "</sspaceex>";
		File f = new File("/home/greitsch/test_with_all.xml");
		
		FileInputStream fis = new FileInputStream(f);

		InputStream is;
		if (f.exists()) {
			is = fis;
		}
		else {
			is = new ByteArrayInputStream(testfile.getBytes());
		}

		Sspaceex sx = (Sspaceex) unmarshaller.unmarshal(is);
		
		Marshaller marshaller = jc.createMarshaller();

		marshaller.setProperty(Marshaller.JAXB_FORMATTED_OUTPUT, Boolean.TRUE);
		
		FileOutputStream fos = new FileOutputStream(new File("/tmp/output.xml"));
		
		marshaller.marshal(sx, System.out);
		marshaller.marshal(sx, fos);
		
		fos.close();
		fis.close();
	}

}
