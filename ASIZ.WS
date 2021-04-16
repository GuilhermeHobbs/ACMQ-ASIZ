.ls1
.rm 73
Prograí ASIÚ ­ Analysió oæ switcheä-currenô filters
­­­­­­­­­­­­­­­­­­­­­­­­­­­­­­­­­­­­­­­­­­­­­­­­­­-

Documentatioî  foò  versioî 1.5®

Introduction
­­­­­­­­­­­-

     Thå ASIÚ prograí analyzeó switcheä-currenô (SI)¬  switcheä-capacétoò 
(SC© filters¬ oò anù periodicallù switcheä Gí-Ã circuiô wherå thå circuiô 
stabilizeó betweeî thå switchinç instants® Thå prograí caî compõte:

Z-transforí transfeò functions.
Poleó anä zeros.
Frequencù responseóº Gain¬ phase¬ anä grouğ delaù (approximated).
Timå responses.
Fråquencù responså sensitivities.
Effectó oæ nonideaì transistoró iî switcheä-currenô circuits.
Erroró duå tï componenô tolåranceó (sensitivitù analysis).
Outpuô frequencù spectrum®

     Thå outputó oæ thå analyseó caî bå plotteä oî thå screeî anä senô tï 
á reporô file® Thå descriptioî oæ thå circuiô tï bå analyzeä ió reaä froí 
á texô file¬ buô alì thå commandó arå giveî interactivelù iî á  gráphicaì 
useò interface.

Input
­­­­-

     Thå circuiô tï bå analyzeä musô bå describeä bù itó smalì-signaì  AÃ 
modeì (thå normaì structurå foò á SÃ circuit¬ anä thå circuiô withouô thå 
biaó  sourceó  foò á SÉ circuit)® Thå circuiô descriptioî ió giveî  bù  á 
texô file¬ iî thå format:

Firsô linå: numbeò oæ nodeó iî thå circuit. 
Followinç lineóº Onå elemenô descriptioî peò line: 

­	MOÓ transistor:
	M<name¾ <draiî node¾ <gatå node¾ <sourcå node¾ <Gm¾ <Gds>
­	Resistor:
	R<name¾ <nodå 1¾ <nodå 2¾ <resistance>
­	Capacitor:
	C<name¾ <nodå 1¾ <nodå 2¾ <numbeò oæ uniô capacitances>
­	Currenô source:
	I<name¾ <nodå +¾ <nodå -¾ <current>
­	Voltagå source:
	V<name¾ <nodå +¾ <nodå -¾ <voltage>
­	Switch:
	S<name¾ <nodå 1¾ <nodå 2¾ <phase¾ [<phase>...]
­	Transconductor:
	G<name¾ <nodå I+¾ <nodå É-¾ <nodå V+¾ <nodå Ö-¾ <Gm>
­	Ideaì operationaì amplifier:
     	O<name¾ <inpuô node¾ <inpuô node¾ <outpuô node>
­	Voltagå amplifiers:
­	E<name¾ <nodå Vo+¾ <nodå Vï-¾ <nodå Vi+¾ <nodå Vï-¾ <Av>Š­	A<name¾ <nodå Vé-¾ <nodå Vi+¾ <nodå Vo¾ <Av>

     Thå  nodeó  arå enumerateä froí ± tï thå numbeò  oæ  nodes¬  withouô 
missinç  numbers® ° ió thå grounä node® Thå phaseó arå enumerateä froí  ± 
tï thå numbeò oæ phases.

     Thå descriptioî caî bå generateä bù thå EdFiì editoò program. 

Modeló foò thå elements
­­­­­­­­­­­­­­­­­­­­­­-

     Thå  MOÓ transistoró caî bå î-channeì oò ğ-channel® Thå AÃ modeì  ió 
thå  samå foò both® Á transistoò ió modeleä bù á transconductancå  Gm¬  á 
Gdó  conduãtancå ¬ á Cgó capacitance¬ anä á Cgä capacitaîce® Gí  anä  Gdó 
arå  giveî  iî thå netlisô file¬ anä thå otheò parameteró caî bå  seô  iî 
severaì wayó iî thå mosfeô parameteró window.

     Resistoró caî bå useä tï converô currentó intï voltageó anä tï modeì 
losseó  iî  switcheó anä DÃ currenô sources® Isolateä capacitoró  caî  bå 
useä iî thå analysió oæ switcheä-capacitoò filters¬ anä thå simulatioî oæ 
parasitiã capacitancå effects® Thå currenô sourceó feeä thå inpuô  signaì 
tï SÉ filters¬ anä voltagå sourceó arå thå inputó foò SÃ filters®  Tranó
conductoró caî bå useä tï modeì OTAs¬ anä otheò functions® Voltagå amplé
fieró  caî  modeì finitå-gaiî operationaì amplifieró iî SÃ  filters¬  anä 
otheò  funãtions® Foò conveniencå iî usinç thå EdFiì editor¬ twï  foòmató 
arå  acceğteä  ("E¢ anä "A")® Ideaì operationaì amplifieró  arå  useä  iî 
switcheä-capacitoò filteró anä iî precisioî switcheä-currenô filters.

     Thå  switchinç perioä ió considereä subdivideä iî á nuíbeò oæ  equaì 
duratioî  phases® Á switcè caî bå opeî oò closeä iî anù oæ theså  phases® 
Thå phaså lisô iî thå descriptioî oæ thå switcè indicateó iî whicè phaseó 
iô ió closed.

     Onlù onå inpuô caî bå applieä tï thå circuit® Severaì signaì sourceó 
caî  exisô iî thå netlist¬ buô thå valueó oæ alì theí arå  considereä  aó 
jusô scalinç factoró foò thå samå inpuô signal.

Output
­­­­­-

     Thå  prograí  computeó nodaì voltageó (iî ú-transform)®  Iî  thå  AÃ 
smalì-signaì  modeì thå relatioî betweeî gatå-sourcå voìtageó  anä  draiî 
currentó oæ MOÓ transistoò ió lineaò (anä thå Cgó anä otheò  capacitanceó 
arå  alsï linear)¬ anä thå outpuô signaì caî bå takeî iî á  switcheä-cuò
renô filteò aó thå gatå voltagå oæ thå transistoò thaô produceó thå  ouô
puô current® Alternatively¬ morå realistically¬ á resistoò caî bå useä tï 
samplå  thå outpuô current® Iî thió case¬ thå resultó arå alsï valiä  foò 
largå signals® 

     Thå  voltageó iî thå adjoinô networë arå alsï available® Iô musô  bå 
observeä thaô somå "voltages¢ iî thå adjoinô networë (aô "higè impådance¢ 
nodes© havå nï physicaì meaning¬ becauså theù belonç tï capacitivå  nodeó 
feä  bù currenô sources® Thoså "voltages¢ arå useä onlù  foò  sensitévitù 
calculations¬  wherå  theiò "infinite¢ valueó arå  multiplieä  bù  "zero¢ 
conductances¬ producinç finitå (anä correct© currenô values® Wheî voltagå Šsourceó  arå used¬ additionaì variableó arå computeä iî thå adjoinô  neô
work¬ indexeä witè numberó abovå thå numberó oæ nïdes® Theù represenô thå 
negativå  oæ thå currentó iî thå voltagå sourceó iî thå adjoinô  network¬ 
anä  arå useä iî sensitivitù calculations® Notå thaô thå adjoinô  networë 
ió  noô  physicallù realizable¬ becauså iî iô thå capacitoró  retaiî  thå 
voltagå oæ thå nexô phase¬ noô oæ thå last.

     Thå voltageó computeä caî bå interpreteä aó thå respoîseó oæ á peré
odicallù  switcheä Gí-Ã circuit¬ wherå thå currentó (and¬ iî  thå  noòmaì 
circuit¬  voltages©  arå alloweä tï reacè thå steadù  statå  betweeî  thå 
switchinç instants.

     Therå  arå restrictionó oî thå topologù oæ thå circuitó thaô caî  bå 
analyzedº Alì thå resistivå portionó musô havå á connectioî tï thå signaì 
grounä aô alì thå phaseó anä currenô sourceó cannoô bå connecteä tï purå
lù  capacitivå nodeó (oò thå prograí wilì producå singulaò equatioî  syó
tems)® Thió normallù happenó iî anù practicaì circuiô topology® 

Prograí operation
­­­­­­­­­­­­­­­­-

Netlist:

     Thå prograí beginó bù presentinç á directorù lisô anä texô fieldó tï 
bå filleä witè thå namå oæ thå inpuô netlisô filå anä thå numbeò oæ  phá
ses®  Thå filå namå caî bå selecteä witè thå mouså iî thå directorù  wiî
dow¬  oò bå giveî iî thå DOÓ commanä line® Thå buttoî "Read¢  startó  thå 
readinç oæ thå file.

Analysis:

     Afteò  thå  reading¬ á windo÷ witè severaì  analysió  parámeteró  ió 
presented®  Usuallù onlù thå outpuô nodå anä thå samplinç parameteró  arå 
used® Thå otheró rarelù musô bå changed® Thå buttoî "Analyze¢ startó  thå 
analysis.

     Aô  thå enä oæ thå analysis¬ thå computeä denominator¬ oò  charaãtå
ristiã  polynomiaì oæ thå circuit¬ ió listed¬ anä arå presenteä á  windo÷ 
witè  numeratoò parameteró anä á menõ witè thå displaù options® Oncå  thå 
numeratoò parameteró arå seô tï thå desireä values¬ thå differenô  analù
seó  iî  thå menõ caî bå madå iî anù order® Thå menõ caî bå  reopeneä  bù 
pressinç thå righô mouså buttoî oî thå framå oæ anù window.

Frequencù response:

     Thå frequencù responså caî bå plotteä foò anù transfeò function®  Iô 
ió plotteä iî thå prograí maiî window¬ witè severaì optionó selectablå iî 
thå frequencù responså parameteró window® Thå samå ploô ió alsï useä  foò 
thå  displaù oæ erroò limitó (sensitivity© anä spectraì  componentó  (seå 
below)® 

Transienô response:

     Timå responseó foò severaì tesô inputó caî bå plotted¬ alsï foò  anù 
transfeò function® Theù arå plotteä iî á secondarù window® Thå  transienô Šresponså parameteró windo÷ holdó thå controló foò thå severaì options.

Poleó anä zeros:

     Poleó anä zeroó oæ anù transfeò functioî caî bå computeä anä plotteä 
iî  á  windo÷ oò listed® Alonç witè thå frequencies¬ thå uniô  circlå  ió 
alsï  plotteä foò reference® Thå poleó anä zeroó parameteró  windo÷  con
troló ho÷ thå poleó anä zeroó arå computeä anä displayed.

Outpuô spectrum:

     Thå  outpuô  spectruí componentó foò á sinusoidaì inpuô aô  á  giveî 
frequencù  caî  bå plotted¬ superimposeä oî thå maiî  frequencù  responså 
plot®  Thå spectruí computatioî caî bå starteä froí thå  outpuô  spectruí 
parameteró  window¬ oò directlù froí thå frequencù responså  window®  Alì 
thå spectruí componentó thaô arå iî thå frequencù rangå selecteä foò  thå 
maiî  transfeò  functioî arå computed® Thå outpuô spectruí  ió  availablå 
onlù foò normaì transfeò functions.

Sensitivity:

     Sensitivitieó froí á transfeò functioî iî relatioî tï thå  variátioî 
oæ  á selecteä grouğ oæ circuiô parameteró caî bå computed¬  anä  ploôteä 
alonç  witè  thå gaiî anä phaså curveó iî thå frequencù  responså  (main© 
window¬  aó  erroró iî decibeló anä degreeó superimposeä  oî  thå  curveó 
shown® Thå erroró caî bå computeä aó deterministiã deviationó (suí oæ thå 
erroró  duå  tï alì thå selecteä parameters©  oò  statisticaì  deviationó 
(squarå  rooô oæ thå suí oæ thå squareó oæ thå erroró duå tï alì thå  så
lecteä  parameters)® Alì thå selecteä parameteró arå assumeä tï havå  thå 
samå variability® Notå thaô thå sensitivitieó oæ jusô onå nodaì  voltage¬ 
thå  onå specifieä iî thå analysió parameteró windo÷ aô thå starô oæ  thå 
program¬  arå  availablå afteò thå initiaì analysis¬  althougè  frequencù 
responseó  oæ anù nodaì voltagå arå alwayó availablå  withouô  recalculá
tion® Thå computátioî oæ erroró duå tï á largå grouğ oæ parameteró maù bå 
slow®  Thå sensitivitieó oæ thå transfeò functioî iî relatioî tï thå  vá
lueó oæ alì thå selecteä elementó caî bå listed¬ bù pressinç "s¢ wheî thå 
cursoò  ió aô thå desireä frequencù iî thå frequencù responså  graph®  Iî 
thå presenô version¬ sensitivitieó foò unsampleä inpuô arå noô  availablå 
(seå "sampling¢ below).

Sensitivitieó witè gaiî sensitivitù discounted:

     Iô  ió possiblå tï discounô thå gaiî sensitivitieó aô á  giveî  fre
quencù  froí thå sensitivitù calculations¬ bù pressinç thå  correspondinç 
settinç  buttoî iî thå sensitivitù analysió parameteró window® Afteò  thå 
initiaì  plot¬  movå thå cursoò tï thå desireä frequencù anä  presó  "s"® 
Thió ió usefuì tï separatå gaiî erroró froí erroró thaô distorô thå  gaiî 
frequencù  response® Thå techniquå ió morå clearlù meaningfuì iî  filteró 
deriveä  froí LÃ doublù terminateä networks¬ wherå aô thå frequencieó  oæ 
maximuí gaiî onlù thå flaô gaiî sensitivitieó affecô thå gain® 

Correlateä elements:

     Foò  thå  statisticaì deviatioî computation¬  groupó  oæ  correlateä 
elementó caî bå specified® Theså elementó havå theiò sensitivitieó  addeä Šanä arå treateä aó á singlå elemenô iî thå computation® Tï selecô  corrå
lations¬  presó onå oæ thå keyó "a".."z¢ beforå selectinç  elementó  witè 
thå  mouså lefô button® Alì thå elementó markeä witè á samå  letteò  wilì 
belonç  tï á grouğ oæ correlateä elements® Tï makå elementó  uncorrelateä 
witè thå others¬ presó thå "*¢ keù beforå selectinç thå elementó witè thå 
mouse® Thå currenô selectioî oæ elementó anä correlationó caî bå saveä tï 
á filå oò reaä back.

References:

     Frequencù  responseó anä transienô responseó caî bå saveä  aó  refå
renceó (thå commandó arå iî thå graphiã windowó menus)¬ anä plotteä alonç 
witè  otheró  oæ thå samå circuiô oò oæ anotheò circuiô  foò  comparison® 
Sensitivitù curveó cannoô bå saveä aó references® Iô ió alsï possiblå  tï 
commanä thå prograí tï dï noô cleaò thå frequencù responså windo÷  beforå 
plottinç  á ne÷ curvå (presó "x")® Iî thió waù anù numbeò oæ  references¬ 
witè erroò curves¬ caî bå accumulated.

Reporô file:

     Thå samå menuó allo÷ thå savinç oæ thå analyseó resultó iî á  reporô 
file®  Thå messageó windo÷ caî alsï bå saveä iî thå reporô file® Foò  thå 
frequencù  response¬  á tablå ió generateä containingº  frequency¬  gain¬ 
phase¬  grouğ  delay¬ gaiî error¬ phaså error¬ minimuí  gaiî  limit¬  anä 
maximuí  gaiî limit¬ aó columnó oæ values® Thå erroró arå listeä onlù  iæ 
thå sensitivitù analysió ió selected.

MOÓ transistoò parameters:

     Iô  ió  possiblå tï includå parasitiã effectó iî thå  circuiô  iî  á 
simplå  waù usinç thå commandó iî thå mosfeô parameteró window®  Oncå  aî 
iteí  ió changed¬ thå circuiô musô bå reaä agaiî anä reanalized® Thå  nå
cessarù windowó opeî automatically.
     
Direcô commanä iî thå windows
­­­­­­­­­­­­­­­­­­­­­­­­­­­­-

Pole/zerï graph:

­ Cursor¬ +¬ -º Movå thå grapè anä changeó thå scale.
­ Mouså middlå buttonº Movå thå cursor.
­ Gº Toggleó thå drawinç oæ á grid.
­ Escº Exitó thå graph.
­ Mouså lefô buttonº Dragginç thå mouså defineó zooí area.

Frequencù responså graph:

­ Horizontaì cursoò oò mouså middlå buttonº Cursor.
­ A¬ R¬ +¬ -º Changå thå horizontaì anä verticaì scales.
­ Verticaì cursor¬ <(,)¬ >(.)º Panning.
­ Lº Changeó thå horizontaì scalå betweeî log® anä linear.
­ Fº Toggleó thå drawinç oæ phaså curves.
­ Tº Toggleó thå drawinç oæ grouğ delaù curves.
­ Vº Listó thå lineaò gaiî aô thå cursoò frequency.
­ Mouså lefô buttonº Dragginç thå mouse defineó zooí area.Š­ Gº Toggleó thå drawinç oæ the grid.
­ Cº Changeó betweeî coloò anä b&÷ picture.
­ Iº Invertó thå colors.
- Sº Lisô alì thå selecteä sensitivitieó aô thå cursoò frequeîcy¬ and,
     if the discount of gain sensitivities is enabled, plots a new graph.
­ Eº Plotó thå spectruí componentó foò aî inpuô aô thå cursoò frequency.
­ Wº Listó thå samå spectrum.
­ Xº Toggleó thå clearinç oæ thå windo÷ beforå thå plotting.
     (Usefuì foò sensitivitù comparisons.)

(G¬ C¬ anä É affecô thå otheò plotó also¬ wheî theù arå redrawn).

Transienô responså graph:

­ Horizontaì cursoò oò mouså middleº Movå thå cursor.
­ A¬ R¬ +¬ -º Changå thå horizontaì anä verticaì scales.
­ Gº Toggleó thå drawinç oæ á grid.

     Thå  direcô commandó iî grapè windowó onlù worë wheî thå graphó  arå 
valid®  Iæ  somå parameteò ió changeä iî somå windo÷ thaô  invalidateó  á 
graph¬ iô remainó unchangeablå untiì redrawn.

     Eacè grapè haó á menõ oæ options¬ presenteä beforå thå plottinç  anä 
alsï accessiblå througè thå grapè menu¬ wherå scáleó anä otheò parámeteró 
caî bå directlù specified.

Observations
­­­­­­­­­­­-

Graphicó modeº

     Thå graphicó modå caî bå specifieä iî thå commanä line¬ iî thå form:
ASIÚ <netlisô file¾ <driver¾ <mode>
Wherå thå driveò anä modå numberó specifù thå BGÉ driveò (Turbï Pascaì 7© 
anä thå modå tï bå useä iî thå plots® Exº ² µ produceó á b&÷ 640x48° modå 
oî VGÁ boards¬ thaô useó littlå memory® Thå defaulô ió 640x480¬ 1¶ coloró 
modå (undeò Windows¬ therå ió nï reasoî tï changå it).

Useò interfaceº

     Thå prograí useó aî interfacå witè graphiã windows¬ wherå thå  mouså 
commandó alì thå actions:
Thå  lefô  buttoî ió useä tï presó buttons¬ selecô menõ  itemó  (eveî  iæ 
presseä  witè  thå mouså ouô oæ thå menõ area)¬ selecô  texô  fieldó  foò 
edition¬ anä movå anä resizå windows.
Thå middlå buttoî closeó á windo÷ iæ presseä oî itó frame® Iô alsï closeó 
menuó withouô selectinç aî item.
Thå righô buttoî openó menus® Therå arå menuó iî mosô oæ thå windowó  (iî 
theiò frames)¬ anä iî thå graphiã areas.
Thå  interfacå  workó witè alì thå graphicó boardó supporteä bù  thå  BGÉ 
drivers® 
Windo÷ movemenô anä openinç caî bå impossiblå duå tï memorù  limitations® 
Thå prograí beepó wheî thió happens.
Thå  prograí  caî bå operateä withouô á mouse® Iæ á mouså driveò  ió  noô 
found¬ aî emulateä mouså appears¬ thaô ió operateä witè thå cursoò  keys® ŠThå  threå  buttonó arå replaceä bù thå returî (left)¬ esã  (middle©  anä 
spacå  (right© keys® Iæ Capó Locë ió active¬ thå keyó operatå  iî  togglå 
modå  (foò  dragging¬ foò exaíple)® Iæ Scrolì Locë ió active¬  thå  mouså 
emulatioî ió disabled¬ sï thå keyboarä caî bå useä normally.
Á twï-buttonó mouså caî alsï bå used® Windowó anä menuó caî bå closeä  bù 
pressinç thå twï buttonó simultaneously.

Poleó anä zeros:

     Thå  defaulô toleranceó anä initiaì approximátionó iî thå poleó  anä 
zeroó parameteró windo÷ arå sufficienô foò mosô usuaì cases¬ buô theù caî 
havå tï bå changeä iî somå cases® Thå mosô usuaì problemó arå witè groupó 
oæ closelù spaceä rootó thaô thå prograí interpretó aó á multiplå rooô oò 
oæ  á  multiplå rooô thaô thå prograí interpretó aó á  grouğ  oæ  closelù 
spaceä  roots® Thå parameteò oæ "magnitudå tolerance¢ caî bå adjusteä  tï 
guidå  thå routinå tï thå correcô resultº Smalleò valueó  forcå  multiplå 
rootó  anä higheò valueó forcå distincô roots® Thå routinå caî alsï  havå 
problemó oæ convergence® Iô wilì loweò thå tolerancå foò thå rootó  untiì 
theù  caî bå found® Poleó anä zeroó arå computeä iî thå  z^(1/f©  domain¬ 
wherå  æ ió thå numbeò oæ phases® Á completå turî arounä thå uniô  circlå 
correspondó tï æ timeó thå switchinç frequency.

Globaì anä Partiaì numerators:

     Thå globaì transfeò functioî oæ á switcheä circuiô witè æ phaseó  ió 
thå compositioî oæ fxæ partiaì transfeò funãtions¬ froí eacè phaså aô thå 
inpuô  tï eacè phaså aô thå output® Thå denominatoò oæ alì thå  functionó 
ió  thå same¬ buô thå numeratoró arå different® Thå prograí computeó  alì 
thå partiaì numeratoró anä addó theí tï obtaiî thå globaì numeratoò  (Thå 
samplinç  operatioî divideó thå suí bù æ iî thå frequencù  response¬  anä 
thå timå separatioî oæ thå phaseó doeó thå samå iî thå transienô  respoî
se®  Duå  tï this¬ thå globaì numeratoò coeæficients¬ aó  listed¬  appeaò 
multiplieä  bù f)® Zeros¬ frequencù respoîses¬ sensitivities¬  anä  tran
sienô reóponseó caî bå computeä foò alì thå partiaì transfeò functions.
     Usuallù thå desiçneä digitaì transfeò functioî oæ á filteò ió onå oæ 
thå partiaì transfeò functions® Notå thaô iî theså caseó thå gaiî appearó 
divideä bù thå numbeò oæ phases¬ aó á partiaì transfeò functioî outpuô ió 
zerï aô thå otheò outpuô phases.

Switcheä-currenô filters:

     Alì thå biasinç DÃ currenô sourceó musô bå omitteä froí thå deócriğ
tioî (rememberº ALÌ thå sourceó arå AC)® Theù caî alsï bå substétuteä  bù 
resistoró råpresentinç theiò outpuô resistances¬ buô iô ió morå practicaì 
tï  seô á convenienô valuå foò Gdó iî thå mosfeô parameteró  window®  Alì 
thå  capacitanceó  anä transconductanceó shalì bå  normalizeä  tï  valueó 
arounä  ± foò gooä accuracù iî thå analysis® Independenô scalinç  factoró 
caî bå useä foò capacitanceó anä transconductances® 

Switcheä-capacitoò filters:

     Finitå-gaiî  voltagå amplifieró anä voltagå sourceó caî bå useä  dé
rectly® Alternatively¬ á cuòrenô sourcå oò á tranóconductoò witè á resió
toò  iî paralleì witè itó outpuô ió equivalenô tï á voltagå sourcå  oò  á 
voltagå amplifier¬ foò capacitivå loads® Notå thaô thå ideaì  operatiïnaì Šamplifieò  ió reallù ideal¬ anä reduceó thå sizå oæ thå systemó oæ  equá
tionó thaô thå prograí solveó wheî used® Impedancå normalizatioî shalì bå 
used¬ witè capacitoró havinç valueó arounä 1.

Sensitivities:

     Iî  propeò  switcheä-currenô filters¬ thå sensitivitieó tï  alì  thå 
capacitanceó arå alwayó nulì (oò low¬ iæ parasitiã capacitances¬ aó  Cgd¬ 
arå included)® Aó default¬ thå prograí markó thå transconductoró tï  havå 
theiò sensitivitieó computed¬ becauså onlù theù arå significanô iî  ideaì 
SÉ filters.

Sampling:

Threå samplinç methodó arå available:

-    Sample/holdº  Thå  inpuô anä outpuô arå considereä  sampleä  aô  thå 
     beginninç oæ eacè phaså anä helä foò thå phaså interval® Thió ió thå 
     usuaì samplinç method® Filteró wilì exhibiô thå usuaì sin(x)/ø  gaiî 
     distortioî causeä bù thå outpuô sampling.

-    Impulseº  Thå inpuô ió considereä sampleä aô thå beginninç  oæ  eacè 
     phaså  anä  helä foò thå phaså interval® Thå  outpuô  ió  considereä 
     sampleä  bù  aî unitarù impulså functioî aô thå  beginninç  oæ  eacè 
     phase®  Filteró  wilì presenô thå ideaì digitaì  transfeò  function® 
     Notå thaô thå prograí assumeó thaô thå outpuô ió sampleä aô alì  thå 
     phases®  Thió caî causå somå confusioî iæ iípulså samplinç ió  used¬ 
     becauså  eveî iæ thå ouôpuô varieó onlù oncå peò period¬ thå  outpuô 
     exhibitó æ impulseó peò påriod® Thió causeó thå appåarancå oæ  extrá 
     zeroó  iî  thå  transfeò  functioî (aô  multipleó  oæ  thå  saíplinç 
     frequency¬  iæ  alì  thå impulseó arå equal)® Thå  artifacô  caî  bå 
     eliminateä bù zeroinç thå outpuô (witè switches© aô alì thå  phases¬ 
     excepô thå onå wherå thå outpuô changes.

-    Nï  samplingº Thå effectó oæ direcô signaì feedthrougè  througè  thå 
     circuiô arå considered® Iô ió assumeä thaô thå timå constantó iî thå 
     patè  arå  negligible¬  sï effectó  oæ  inpuô  variationó  propagatå 
     instantaneously® Frequencù responses¬ transienô responses¬ anä spec
     trá wilì bå computeä considerinç thå signaì feedthrough® Sensitivitù 
     analysió ió noô availablå (yet© iî thió case®

     Notå thaô otheò samplinç methodó caî bå analyzed¬ bù usinç  expliciô 
samplinç circuitó addeä tï thå inpuô oò output® Á sample/holä circuiô caî 
bå madå witè á switch¬ á capacitor¬ anä á buffeò circuit.

Outpuô spectrum:

     Foò usuaì filters¬ thå outpuô spectruí componentó appeaò aô alì  thå 
frequencieó  iî thå forí n<samplinç frequency>+¯-<inpuô  frequency>¬  anä 
thå amplitudeó agreå witè thå maiî transfeò functioî amplitudeó aô  thoså 
frequencies®  Thió  ió noô alwayó true¬ becauså  modulatioî  effectó  caî 
affecô  thå spectruí components¬ causinç somå oæ theí tï disappeaò oò  tï 
assumå differenô values® Thå prograí takeó alì theså effectó intï  consé
deration.
ŠGrouğ delay:

    Thå  grouğ delaù ió computeä bù thå numericaì differentiatioî oæ  thå 
phaså curves¬ anä sï ió morå preciså iæ morå pointó arå used® (Thå  exacô 
computatioî ió possible¬ anä wilì bå includeä iî á futurå version.©  Spi
keó  maù appeaò aô 36° degreeó phaså transitionó iæ noô  enougè  segmentó 
arå used.

Circuitó witè cancelleä unstablå poles:

    Iæ á transfeò functioî haó cancelleä poleó ouô oæ thå uniô circle¬ aó 
happenó  witè balanceä structureó withouô commoî-modå feedback¬ thå  prï
graí  caî  havå problemó wheî plottinç thå transienô  response®  Usually¬ 
numericaì  residueó oæ thå analysió wilì excitå thå unstablå  poles¬  anä 
thå  transienô responså wilì divergå afteò somå time® Thå effecô ió  verù 
dependenô  oî numericaì details¬ aó thå interpolatioî radiuó  used®  Notå 
thaô theså circuitó havå onlù theoreticaì interest® Thió notå ió jusô  tï 
explaiî thå apparenô error.

Valiä resultsº

     Iô musô bå noteä thaô thå prograí assumeó thaô alì thå elementó  arå 
lineaò (smalì-signaì model)® Thå resultó arå valiä foò largå signaló onlù 
iæ certaiî topologiã restriãtionó (switcheä-currenô oò switcheä-capacitoò 
techniques© arå followed® Also¬ thå prograí assumeó thaô switchinç  traî
sientó  arå mucè fasteò thaô thå switchinç period¬ and¬ oæ  course¬  thaô 
thå continuouó-timå circuitó formeä iî anù phaså arå stable.

Analysió methodº

     Thå analysió methoä useä bù thå prograí waó describeä iî thå  paperº 
"Systematiã  nodaì analysió oæ switcheä-currenô filters,¢ bù A® C® M®  då 
Queiroz¬  P®  R® M® Pinheiro¬ anä L® P® Caloba¬ proceedingó oæ  thå  199± 
IEEÅ ISCAS¬ Singapore¬ pp® 180±-1804¬ Junå 1991® Á morå detaileä deócrip
tioî appeareä iî thå papeò "Nodaì analysió oæ switcheä-currenô  fiìters,¢ 
IEEÅ  Transactionó oî Circuitó anä Systemó-II¬ vol® 40¬ no®  1¬   Jánuarù 
1993¬  pp®  1°-18¬ anä á stilì morå detaileä descriptioî ió iî  thå  booë 
"Switcheä-Currentsº Aî Analoguå Techniquå foò Digétaì Technology"¬ editeä 
bù  C® Toumazou¬ N® C® Battersby¬ anä J® B® Hughes¬ anä publisheä bù  thå 
IEÅ iî 1993® 

Protecteä modeº

     Thå  ASIÚ prograí workó iî protecteä modå oî á PÃ witè á  286¬  386¬ 
486¬ oò Pentiuí processor¬ witè extendeä memory® Iô caî bå executeä undeò 
Windowó  9ª  oò  undeò DOS/Windowó 3*¬ buô iî thå lateò  caså  thå  fileó 
RTM.EXÅ  anä DMPI16BI.OVÌ musô bå presenô oî thå DOÓ path¬ oò somå  otheò 
DPMÉ driveò musô bå installed® Á reaì modå versioî oæ thå program¬  nameä 
ASIÚ-R¬  ió alsï includeä iî thå distribution® Iô doesn'ô  requirå  DPMI¬ 
buô  cannoô uså alì thå availablå memory¬ anä sï cannoô analyzå biç  cir
cuits.

Maiî revisions:
Versioî 1.5º Discounô oæ gaiî sensitivitieó implemented.
Versioî  1.4dº  Bugó  iî thå treatmenô oæ voltagå  sources¬  noiså  inpuô Š     withouô  sampling¬  anä á possiblå causå oæ crasè iî  thå  transienô 
     plottinç removed® Single-precisioî versioî oæ thå prograí removed.
Versioî 1.4cº Noiså inpuô iî thå transienô responså added.
Versioî 1.4bº Timå limiô iî thå transienô responså eliminated.
Versioî  1.4aº Approximatå grouğ delaù computatioî included¬ anä  listinç 
    oæ  thå  gaiî  values¬  foò easù dynamiã  rangå  equalizatioî  oæ  SÉ 
    filters.
Versioî  1.4º  Direcô  signaì feedthrougè  considered¬  witè  thå  "None¢ 
    samplinç  option®  Generaì  rewrittinç oæ  internaì  procedures®  Thå 
    transienô responseó saveä iî thå reporô no÷ contaiî thå valueó aô thå 
    twï extremeó oæ eacè phaså interval¬ anä wilì ploô correctlù iî á  XÙ 
    plotteò program.
Versioî 1.3aº Aî optimizatioî iî numericaì procedureó increaseä  signifé
    cantlù thå analysió speed® ²-3ø foò twï-phaseó circuits¬ anä morå foò 
    morå phases.
Versioî 1.3º Outpuô spectruí calculatioî included® Retaininç oæ thå  fre
    quencù  responså grapè (commanä "X"© added® Correcteä potentiaì  pro
    bleí iî thå savinç oæ thå sensitivitù selection.
Versioî 1.2dº Correcteä á buç iî thå numbeò oæ phaseó iî references.
Versioî 1.2cº Frequencù responseó anä sensitivitieó arå no÷ availablå foò 
    thå partiaì transfeò functions® Thå sensitivitù calculatioî waó opti
    mézed¬ anä ió no÷ ² oò ³ timeó faster.
Versioî 1.2bº Thå impulså inpuô no÷ lastó foò onå entirå period¬ anä  thå 
    plottinç oæ thå inpuô iî thå transienô responså ió optional.
Versioî 1.2aº Morå correlateä groups® Mosô recenô versionó coípileä  witè 
    slightlù changeä interface.
Versioî 1.2º Groupó oæ correlateä elementó iî thå statisticaì deviation.
Versioî 1.1bº Sensitivitieó caî bå listed.
Versioî 1.1aº Voltagå sourceó included.
Versioî  1.1º Memorù allocatioî improveä tï allo÷ thå analysió oæ  largeò 
    circuits® Thå prograí no÷ acceptó circuitó oæ uğ tï 20° nodeó anä  1¶ 
    phases¬ resultinç iî systemó oæ uğ tï 40° equátions.

Fileó oî thå compresseä distributioî file
­­­­­­­­­­­­­­­­­­­­­­­­­­­­­­­­­­­------

ASIZ.EXÅ ­ Thå basiã SÉ analysió program¬ protecteä mode.
ASIÚ-R.EXÅ ­ Real-modå version® Foò simpleò machines.
ASIZ.TXÔ ­ Documentatioî foò thå ASIÚ program.
EXAMPLES.TXÔ ­ Descriptioî oæ thå examples.
EDFIL.EXÅ ­ Circuiô schematiã editor.
RTM.EXÅ ­ Useä bù protecteä modå programs® Musô bå iî thå path.
DMI16BI.OVÌ ­ Necessarù wheî noô undeò Windowó 9*® Musô bå iî thå path.
*.BGÉ ­ Turbï Pascaì · graphicó drivers® Musô bå oî á patè pointeä bù thå 
DOÓ environmenô variablå "TPBGI".
LITT.CHÒ ­ Smalì fonô file® Idem.
*.CIÒ ­ Schematiã circuiô fileó foò EdFil.
*.NEÔ ­ Netlisô files.
*.VAÌ ­ Valuå lisô fileó foò Edfil.

Speciaì versions
----------------

     Versionó oæ thå ASIÚ anä EdFiì programó compileä witè GNÕ Ã  (djgpp© 
arå alsï availablå froí thå samå site® Theså programó accepô largeò  ciòŠcuits® Thå X_EdFiì prograí useó aî interfacå aó thå onå oæ thå ASIÚ  prï
gram¬  anä  thå X_ASIÚ prograí ió somewhaô fasteò thaî  thå  normaì  ASIÚ 
program® Iô operateó exactlù iî thå samå way.
     Versionó  oæ thå ASIÚ anä EdFiì programó foò UNIX¬ iî  Suî  workstá
tionó  anä  undeò Linuø iî PCs¬ arå alsï available® Theù  operatå  almosô 
exactlù  aó  thå PÃ versions¬ usinç thå XVie÷ Opeî-Looë  interface®  Thió 
manuaì  ió alsï valiä foò thå UNIØ ASIÚ version¬ witè slighô  changeó  iî 
thå interfacå operation® Thå prograí haó á oî-linå helğ systeí thaô  coî
tainó mosô oæ thå informationó iî thió text.

Distributioî anä use
­­­­­­­­­­­­­­­­­­­-

     Thå ASIÚ prograí caî bå distributeä freelù foò educatiïnaì purpïses¬ 
aó lonç aó nï chargå ió made¬ iô ió noô changeä iî anù way¬ anä referencå 
tï itó uså ió madå iî anù worë donå witè itó help.
     Foò commerciaì utilization¬ á registratioî feå ió required®  Coîtacô 
thå author® 
     Thå  authoò  believeó thaô thå prograí workó correctly¬  buô  cannoô 
assumå  responsibilitù  foò losseó causeä bù flawó iî  thå  prograí  thaô 
escapeä hió attention.
     Thå  mosô currenô versioî oæ thå prograí anä auxiliarù fileó caî  bå 
obtaineä bù "anonymouó ftp¢ iî thå Internet¬ aô thå directorù  "pub/acmq¢ 
aô thå sitå "coe.ufrj.br"¬ oò througè thå Worlä Widå Web¬ at:
http://www.coe.ufrj.br/~acmq/ASIZ.html.
     Useró  arå encourageä tï senä á letteò oò å-maiì tï thå authoò  tel
linç ho÷ thå prograí ió beinç used.
     Comments¬  suggestionó anä questionó abouô thå  prograí  utilizatioî 
shalì bå senô to:

Dr® Antoniï Carloó M® då Queiroz
Programá då Engenhariá Eletrica
COPPÅ ­ Universidadå Federaì dï Riï då Janeiro
CĞ 68504
2194µ-970¬ Riï då Janeiro¬ RJ¬ Brazil

or¬ viá å-mail¬ tï acmq@coe.ufrj.br

26/07/1998
