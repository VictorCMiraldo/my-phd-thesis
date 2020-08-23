De \unixdiff{} tool -- die het verschil tussen twee bestanden berekent
in termen van de verzameling regels die gekopieerd worden -- wordt
veel gebruikt bij het versiebeheer van software. De vaste
granulariteit, \emph{regels code}, is helaas soms te grof en verhult
eenvoudige wijzigingen. Bijvoorbeeld, door het hernoemen van een
parameter van een functie kunnen vele verschillende regels
veranderen. Dit kan leiden tot onnodige conflicten wanneer
ongerelateerde wijzigingen toevallig op dezelfde regel code
plaatsvinden. Het is daarom lastig om zulke wijzigingen automatisch te
combineren.

Traditionele methodes om verschillen te bepalen tussen een bronbestand en doelbestand
\cite{Bille2005,Bergroth2000,Paassen2018,McIlroy1976,Myers1986,Hirschberg1975}
maken gebruik van een \emph{edit-script}, die de veranderingen
documenteren om het bronbestand in het doelbestand te transformeren. Zulke
edit-scripts bestaan uit een reeks edit-operaties, zoals het invoegen,
verwijderen of kopie\"eren van een regel. Beschouw bijvoorbeeld de
volgende twee bestanden:

{
\footnotesize
\begin{minipage}{.45\textwidth}
\begin{alltt}
1    res := 0;
2    for (i in is) \{
3      res += i;
4    \}
\end{alltt}
\end{minipage}\qquad%
\begin{minipage}{.45\textwidth}
\begin{alltt}
1    print("summing up");
2    sum := 0;
3    for (i in is) \{
4      sum += i;
5    \}
\end{alltt}
\end{minipage}
}

Regels 2 en 4 in het bronbestand links komen overeen met regels 3 en 5
in het doelbestand rechts. Deze worden dan ook ge\"{i}dentificeerd als
kopie\"en. De overige regels worden verwijderd of ingevoegd. In dit
voorbeeld worden regels 1 en 3 uit het bronbestand verwijderd; regels
1,2 en 4 worden in het doelbestand ingevoegd.

Deze informatie over welke afzonderlijke regels zijn gekopieerd,
verwijderd of ingevoegd wordt dan samengebracht in een edit script:
een lijst operaties die een bronbestand transformeert in een
doelbestand. In het voorbeeld hierboven, zou het edit-script bestaan
uit een serie edit-operaties als: verwijder een regel; voeg twee
nieuwe regels in; kopieer een regel; verwijder een regel; enz. De
uitvoer van \unixdiff{} bestaat uit zo'n lijst
operaties. Verwijderingen worden aangeduid door een regel te beginnen
met een minteken; invoegingen worden aangeduid met een plusteken. In
ons voorbeeld zou het resultaat van \unixdiff{} bestaan uit de
volgende regels:
\begin{alltt}\footnotesize
-    res := 0;
+    print("summing up");
+    sum := 0;
     for (i in is) \{
-      res += i;
+      sum += i;
     \}
\end{alltt}

Er bestaan veel generalisaties van edit-scripts die niet werken met
regels code, maar bomen
\cite{Zhang1989,Demaine2007,Dulucq2003,Pawlik2012,Augsten2008,Augsten2010},
maar veel van dit werk heeft significante nadelen. Om te beginnen,
edit-scripts zijn niet in staat om willekeurige permutaties,
duplicaties, of contracties (de inverse van duplicaties) uit te
drukken. Ten tweede, hebben de meeste van deze algoritmen een
significant slechtere \emph{performance} dan \unixdiff. Tot slot,
houdt het meeste van dit werk zich bezig met \emph{ongetypeerde}
bomen, dat wil zeggen, dat ze geen garanties geven over of de
resulterende edit-scripts een zekere structuur, ook wel bekend als een
\emph{schema}, behoudt. Het is mogelijk om getypeerde edit-scripts te
ontwerpen~\cite{Lempsink2009}, maar dit pakt nog niet alle
bovengenoemde nadelen aan.

In dit proefschrift bespreken we twee nieuwe manieren om het verschil
te bepalen tussen `gestructureerde data', zoals bomen, die zich niet langer
beperken tot alleen edit-scripts. De eerste aanpak definieert een
type-ge\"{\i}ndexeerde representatie van wijzigingen en geeft een helder
algoritme om twee verschillende wijzigingen samen te voegen, maar is
helaas computationeel te duur om bruikbaar te zijn. De tweede aanpak
is een stuk effici\"enter door het kiezen van een meer extensionele
representatie van wijzigingen. Hierdoor kunnen we allerlei
transformaties uitdrukken die gebruik maken van invoegingen,
verwijderingen, duplicaties, contracties en permutaties, en deze in
lineaire tijd berekenen.

Stel, we moeten een wijziging beschrijven in de linkerdeelboom van een
binaire boom. Als we een hele programmeertaal zoals Haskell tot onze
beschikking zouden hebben, zouden we iets kunnen schrijven als de
functie |c| in \Cref{fig:sammenvatting:example-01:A}. Merk hierbij
op dat deze functie een duidelijk domein heeft -- de verzameling bomen
die, wanneer |c| erop toegepast wordt een |Just| constructor
opleveren. Dit domein wordt bepaald door de patronen en ``guards'' die
de functie |c| gebruikt. Zo bepalen we voor elke boom in dit domein,
een bijbehorend resultaat in het codomein. Deze nieuwe boom kunnen we
bepalen door in de oude boom de waarde 10 te vervangen door 42. Bij
nadere inspectie, zien we dat we het pattern-matchen op de invoerboom
kunnen opvatten als het (mogelijk) \emph{verwijderen} van bepaalde
deelbomen; de constructie van de resultaatboom kunnen we beschouwen
als het \emph{invoegen} van nieuwe deelbomen. Het \texttt{hdiff}
algoritme dat wij in dit proefschrift ontwikkelen representeert een
wijziging |c| dan ook als een patroon en een expressie. Zo kunnen we
de wijziging van |c| beschrijven als |Chg (Bin (Leaf 10) y) (Bin
(Leaf 42) y)| -- zoals we illustreren in 
\Cref{fig:sammenvatting:example-01:B}.

\begin{figure}
\centering
\subfloat[Haskell functie |c|]{%
\begin{myhsFig}[0.4\textwidth]
\begin{code}
c :: Tree -> Maybe Tree
c (Bin (Leaf x) y)
  | x == 10    = Just (Bin (Leaf 42) y)
  | otherwise  = Nothing
c _            = Nothing
\end{code}
\end{myhsFig}\label{fig:sammenvatting:example-01:A}}\qquad\qquad
\subfloat[|c| gerepresenteerd als een \emph{wijziging}]{%
\begin{myforest}
[,change
[|Bin|
  [|Leaf| [|10|]]
  [y,metavar]]
[|Bin|
  [|Leaf| [|42|]]
  [y,metavar]]
]
\end{myforest}\label{fig:sammenvatting:example-01:B}}
\caption{Een Haskell functie en de bijbehorende grafische
  representatie als wijziging.  Deze wijziging past de linkerdeelboom
  van een binaire knoop aan. De notatie |metavar y| wordt gebruikt om
  aan te geven dat |y| een metavariabele is.}
\label{fig:sammenvatting:example-01}
\end{figure}

Doordat onze wijzigingen een rijkere expressiviteit genieten, wordt
het samenvoegen van zulke wijzigingen complexer. Als gevolg hiervan
wordt het algoritme om twee wijzigingen te verenigen ingewikkelder en
kan het soms lastiger worden om over de wijzigingen te redeneren.

Deze twee verschillende algoritmes om het verschil tussen
gestructureerde data te berekenen kunnen worden toegepast op
wederzijds recursieve datatypes, met als gevolg dat ze gebruikt kunnen
worden om computerprogramma's te vergelijken. Om dit te implementeren
was niet eenvoudig, en we hebben in de context van
dit proefschrift dan ook verschillende nieuwe bibliotheken voor
generiek programmeren in Haskell ontwikkeld.

Tot slot, hebben we een empirische evaluatie van onze algoritmes
uitgevoerd aan de hand van conflicten die we hebben verzameld van
\texttt{GitHub}. Uit deze evaluatie blijkt dat ten minste
\qSolvedPerc{} van de conflicten die softwareontwikkelaars dagelijks
tegenkomen, voorkomen hadden kunnen worden met de technologie die in
dit proefschrift ontwikkeld wordt. Dit doet vermoeden dat er nog veel
winst te behalen is in het gebruik van betere algoritmes als basis
voor het versiebeheer van software.
