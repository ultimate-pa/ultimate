# Motivation
Dieses Dokument soll dabei helfen, [ANTLR](https://github.com/antlr/antlr4) in [ultimate](https://github.com/ultimate-pa/ultimate) einzubinden, um aus LLVM-IR Code einen AST zu generieren, der im späteren Verlauf des Projektes in einen Boogie AST übersetzt werden soll.

# Lizenzhinweis
[ANTLR](https://github.com/antlr/antlr4) verwendet die [BSD-3-Clause-Lizenz](https://github.com/antlr/antlr4/blob/dev/LICENSE.txt), daher muss darauf geachtet werden, dass Copyright und Lizenztext im ultimate Repo wiedergegeben werden. Des Weiteren muss im ANTLR-Quellcode bzw. im generierten Parser durch geeignete Kommentare kenntlich gemacht werden, welche Stellen angepasst wurden. Außerdem sollte der Lizenzheader im Code erhalten bleiben.
[ANTLR](https://github.com/antlr/antlr4) bzw. dessen Autoren dürfen ebenfalls nicht als Unterstützer, Sponsor oder Befürworter des Projekts dargestellt werden.

# Integration
Die Integration erfolgt über eine `.g4`-Datei im Repository. Der Java-Parser wird beim Build-Prozess automatisch generiert und nicht fest im Repository mitgeführt.
#### ANTLR4-Maven-Plugin 
ANTLR4 wird über das [ANTLR4-Maven-Plugin](https://www.antlr.org/tools.html) eingebunden. Dieses sorgt dafür, dass beim Build automatisch Java-Klassen aus der `.g4`-Datei erstellt werden.
Die notwendigen Einträge in der `pom.xml` sehen wie folgt aus:
```xml
<build>
  <plugins>
    <plugin>
      <groupId>org.antlr</groupId>
      <artifactId>antlr4-maven-plugin</artifactId>
      <version>4.13.2</version>
      <executions>
        <execution>
          <goals>
            <goal>antlr4</goal>
          </goals>
          <configuration>
            <visitor>true</visitor>
            <listener>true</listener>
          </configuration>
        </execution>
      </executions>
    </plugin>
  </plugins>
</build>

<dependencies>
  <dependency>
    <groupId>org.antlr</groupId>
    <artifactId>antlr4-runtime</artifactId>
    <version>4.13.2</version>
  </dependency>
</dependencies>
````

#### Gramatikdatei
[ANTLR](https://github.com/antlr/antlr4) verwendet `.g4`-Dateien zur Beschreibung von Grammatiken. Die gegebene [LLVM-IR Grammatik](https://github.com/antlr/grammars-v4/blob/master/llvm-ir/LLVMIR.g4) muss deshalb im Repository aufgenommen werden.
#### Build-Prozess
Beim Build werden die generierten Dateien in einem Ordner namens `gen` abgelegt. Dieser wird in der Regel vom ANTLR-Maven-Plugin als ''generated source'' erkannt und von der IDE korrekt eingebunden. Falls dies nicht automatisch geschieht, sollte der `gen`-Ordner manuell als ''Generated Source Root'' markiert werden, damit die Klassen vom Compiler und der IDE erkannt werden.
#### Besucherklassen
[ANTLR](https://github.com/antlr/antlr4) generiert optional sogenannte **Listener-Klassen** nach dem Listener-Pattern. Wenn in der Plugin-Konfiguration `listener=true` gesetzt ist, entstehen folgende Klassen:
- `LLVMIRBaseListener.java` - enthält leere Default-Implementierungen für alle enter- und exit-Methoden
- `LLVMIRListener.java` - Interface mit allen enter- und exit-Methoden für die ParseTree-Knoten

Zur Weiterverarbeitung des Parse Trees kann eine eigene Listener-Klasse angelegt werden, welche von dem BaseListener erbt. 

#### Meeting-Notizen
##### Ultimate Aufbau
Jedes Projekt in Ultimate besteht aus 3 Klassen (bzw. 2 - abhängig davon ob es ISource oder ITool ist):
- Activator (oft nur 2 Strings)
- Etwas, dass ISource oder ITool immplementiert
- Observer (nur bei ITools): Wird erzeugt - die process Methode darin wird aufgerufen. Diese erzeugt aus einem Ultimate Model ein anderes

##### Wie sollen die neuen Plugins aussehen?
Es werden im Laufe des StuPro mind. 3 Plugins erstellt. Zwei davon sind Parser (einer von C und eins von LLVMIR), ein weiteres wird die Übersetzung von LLVM-IR ParseTree zu einem Boogie AST übernehmen.
**Parser:**
- C -> LLVM-IR ParseTree und LLVM-IR -> LLVM-IR ParseTree
- Müssen ISource (bzw. Unterklasse) implementieren. 
- Sollen den gleichen Output liefern - heißt bei beiden müssen die LLVM-IR Optimierungen durchgeführt werden, vor der Umwandlung zum ParseTree über ANTLR.
- Der Output wird der ParseTree vom LLVM-IR sein.
- Dieser Output muss als IElement zurückgegeben werden - dafür muss eine neue Klasse erstellt werden, beiu der IElement als Wrapper für einen ParseTree fungiert.
- Zur Hilfe die Beispiele betrachten

**Übersetzungs-Plugin:**
- Muss ITool (bzw. Unterklasse) implementieren.
- Nimmt den ParseTree als Input.
- Erzeugt Boogie AST.
- Zur Hilfe das Beispiel betrachten (CACSLToBoogieTranlator - ist ein IGenerator, der Observer wird darin erzeug)

**Benennung der Plugings:**
- LlvmirParser
- CToLlvmirParser
- LlvmirToBoogie

##### Mögliche Probleme
Es könnte sein, dass im späteren Verlauf ein weiteres Projekt erstellt werden sollte, in dem alles nötige für ParseTree ist (Library-Llvmir; siehe andere Library Projekte).
Zunächst wird allerdings alles in den LLVM-IR Parser gepackt.

##### ToDos
**Vorbereitungen:**
- Nachschauen wie das übergeben von ParseTrees in ANTLR funktioniert.
- Nachschauen ob es möglich ist Clang und die Optimierungen ohne das erstellen von tmp Dateien auszuführen (Erster Ansatz: Standard Input)

**Implementierung:**
- Branch erstellen
- Projekt erstellen
- Implementieren des LLVM-IR Parsers beginnen

----
# Dokumentation des Integrationsprozesses
#### Vorbereitung
**Nachschauen wie das übergeben von ParseTrees in ANTLR funktioniert:**
Bei der Recherche ist aufgefallen, dass ein Listener statt einem Visitor nötig ist um die enter/exit Funktionen zu nutzen - diese Änderung wurde bereits oben im Dokument angepasst.

Ein `ParseTree` kann folgendermaßen erstellt werden:
```java
CharStream input = CharStreams.fromFileName("test.ll");
LLVMIRLexer lexer = new LLVMIRLexer(input);
CommonTokenStream tokens = new CommonTokenStream(lexer);
LLVMIRParser parser = new LLVMIRParser(tokens);
		
ParseTree tree = parser.compilationUnit();
````
Beachte: `comilationUnit` ist der Startknoten. Dieser ParseTree kann nun weiter übergeben werden. 
Ein Beispiel bei dem der ParseTree abgelaufen wird:
```java
public static void testParseTreeParameter(ParseTree tree) {
	ParseTreeWalker.DEFAULT.walk(new LlvmirToBoogieListener(), tree);
}
````
Dabei definiert die `LlvmirToBoogieListener` Klasse was beim betreten/verlassen der einzelnen Knoten passiert. Hier wird die Übersetzung zu einem Boogie AST stattfinden. 

**Nachschauen ob es möglich ist Clang und die Optimierungen ohne das erstellen von tmp Dateien auszuführen:**
Es ist möglich. Bei der Übersetzung von `.c` Dateien muss noch identifiziert werden, wie `assert.h` am besten eingebunden wird, da das ohne Zusatz zu einem Fehler führt.
Die Optimierung einer `.ll` Datei kann folgendermaßen implementiert werden:
```java
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.ByteArrayOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.OutputStreamWriter;

public class LlvmirOptPipeline {
	public static String readAndOptLlFile(String filename) throws IOException, InterruptedException {
		// .ll-Datei einlesen und "optnone" entfernen
		ByteArrayOutputStream cleanedLl = new ByteArrayOutputStream();
		try (BufferedReader reader = new BufferedReader(new FileReader(filename));
				BufferedWriter writer = new BufferedWriter(new OutputStreamWriter(cleanedLl))) {
			String line;
			while ((line = reader.readLine()) != null) {
				writer.write(line.replace("optnone", ""));
				writer.newLine();
			}
			writer.flush();
		}

		// opt-Prozess starten
		ProcessBuilder opt = new ProcessBuilder("opt", "-S", "-passes=sroa,mem2reg,simplifycfg", "-o", "-");
		Process optProc = opt.start();

		// Bereinigte .ll-Datei an opt übergeben
		try (OutputStream out = optProc.getOutputStream()) {
			cleanedLl.writeTo(out);
		}

		// Ergebnis von opt auslesen und ausgeben
		ByteArrayOutputStream result = new ByteArrayOutputStream();
		try (InputStream in = optProc.getInputStream()) {
			in.transferTo(result);
		}
		optProc.waitFor();

		return result.toString("UTF-8");
	}
}
````
Ersetzt man bei der Erstellung des ParseTrees nun
```java
CharStream input = CharStreams.fromFileName("test.ll");
```` 
durch 
```java
CharStream input = CharStreams.fromString(LlvmirOptPipeline.readAndOptLlFile("input.ll"));
````
kann mit dem optimierten Code weiter gearbeitet werden ohne in jemals zwischenzuspeichern.

#### Implementierung
Branch: wip/pr/antlr_integration

Über die build.xml wird mit der `lib/antlr-4.13.2-complete.jar` der LLVMIR Lexer und Parser, sowie die weiterhin relevanten dateien, erzeugt und im `src/de/uni_freiburg/informatik/ultimate/llvmir/parser` Verzeichnis abgelegt. Zudem wird jeder `.java` die benötigte package Signatur hinzugefügt.

In `UltimateLlvmirParser` wird die hauptfunktionalität des Plugins implementiert, d.h. die Übersetzung der `.ll`-Datei in einen ParseTree. Dieser muss als `IElement` übergeben werden, weshalb die Klasse `ParseTreeElementWrapper` benötigt wird. Der ParseTree wird darin als Feld gespeichert. Um die Informationen Abzufragen muss ein Cast verwendet werden.
