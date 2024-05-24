
report =: dyad define
  which=.x [ cond=.y
  ind=: (+./ cond , which { ind) (;/which)} ind  NB. ind[which]←∨/ind[which],cond
)

i =: monad define
  NB. invalid operation
  Invop report 1
)

NB.-----------------------------------------------
NB. representation and interpretation functions --
NB.-----------------------------------------------

magni=: monad define
  NB. interpretacion de magnitud
  rep=.y
NB.   big=. 1;1x
NB.   l=. 0 { _1{.$rep
NB.   f=.0{>(l>53){big
NB.   (radix*f)#."1 rep
  l=. 0 { _1{.$rep
  radix#."1 rep
)

magn0i=:monad define
  NB. interpretacion de magnitud high zero
  rep=.y
NB.   big=. 1;1x
NB.   l=. 0{_1.{.$rep
NB.   f=. 0{>(l>53){big  NB. Coerci'on a big integer
NB.   modulus=. (radix*f)^l 
  l=. 0{_1.{.$rep
  modulus=. radix^l 
  value=. magni rep
  value+modulus*value=0
)

signmagni=: monad define 
  NB. interpretacion signo magnitud
)

radixcompi=: monad define
  NB. interpretacion complemento a la raiz
  rep=.y
NB.   big=. 1;1x
NB.   l=. 0{_1.{.$rep
NB.   f=. 0{>(l>53){big  NB. Coercion to big integer
NB.   modulus=.(radix*f)^l
NB.   print modulus
  l=. 0{_1.{.$rep
  modulus=.radix^l
NB.   value=.(radix*f) #."1 rep
  value=.radix #."1 rep
  number=.value-(value >: modulus % 2)*modulus
)

digitcompi=: monad define
)

magnr=: dyad define
  NB. representacion de magnitud
  size=.0{,x
  number=.y
  (size$radix)#:number
)

signmagnr=: dyad define
)

radixcompr=:dyad define
  NB. representacion complemento a la raíz
  size=.0{,x
  number=.y
NB.   big=.1;1x
NB.   f=. 0{>(size>53){big  NB. Coercion to big integer
NB.   modulus=.(radix*f)^size
  NB. domain signals
  modulus=.radix^size
  xmax=:number>:modulus%2
  xmin=:number<-modulus%2
  rep=. (size$radix)#:number
)

digitcompr=: dyad define
)


NB.------------------------------
NB.-- floating-point functions --
NB.------------------------------

biasi=: monad define
)

biasr=: dyad define 
)

hidebit=: monad define
)

insertbit=: monad define
)

truncate=: monad define
)

round=: monad define
)

trueround=: monad define
)

normalize=: dyad define
)

flbsi=: monad define
)

flbsr=: dyad define
)

NB.-------------------------
NB.-- character functions --
NB.-------------------------


wide=: dyad define
  size=.0{,x
  in=.y
  NB. ajuste de ancho
  dim=.(>.($,in)%size),size
  NB. extend with zero as needed
  dim $(-*/dim) {.,in 
)

fld=: monad define
  field=.y
  NB. instruction field decoding
  magni field{inst
)

fld0=:monad define
  field=.y
  NB. instruction field decoding
  magn0i field{inst
)

fldOff=: monad define
  field=.y
  NB. instruction field decoding
  radixcompi field{inst
)

carryfrom=: dyad define
  expmod=. x
  operands=.y
  NB. carry in addition
  (radix^expmod)<:+/(radix^expmod)|/operands
)

NB.-----------------------------------------------
NB.-- Machine Language Interpretation functions --
NB.-----------------------------------------------

decode=: monad define NB. r←decode inst;f;type
  NB. opcode decoding
  NB. M0 opcode 10 -x- 01 uno 00 cero
  inst=.y
  f=.(<(<0$0);(i.$inst)){form            NB. f=form[;⍳⍴inst;]
  typ=. +/ +./\. 1 }.((*./" 1(+./"1 f) >:"1 1 inst) *. (*./"1 (</"1 f) <:"1 1 inst)) NB. +/∨\⌽1↓(((∨/f)∧.≥ inst) ∧ (</f)∧.≤ inst)
  (typ{orop)+magni (*./"1 typ{form)#inst                        NB. orop[type]+magni (∧/form[type;;])/inst
)

execute=: monad define
  NB. instruction execution
  inst=: y
  ". ((decode inst) { oplist), ''''''   NB.  ⍎ ⍕oplist[decode inst;]
  1
)

NB.------------------
NB.-- Architecture --
NB.------------------

initiateM0=:monad define
  NB. Iniciacion de la M0
  formatM0 ''
  configureM0 ''
  spaceM0 ''
  nameM0 ''
  controlM0 ''
  NB. dataM0
)
 
formatM0=: monad define
  NB. unidades de informacion de la M0
  NB. radix de representacion
  radix=:2
  NB. unidades de informacion
  byte=:  8
  word=: 24
  dir=:  16
  NB. capacidad de direccionamiento
  adrcap=:radix^dir
)

configureM0=: monad define
  NB. configuracion de la M0
  NB. capacidad de memoria
  memcap=:radix^dir
)


regoutM0=: monad define
	direg=.y
	select. direg
	case. dirPc do.
		value=. Pc
	case. dirB do.
		value=. B
	case. dirX do.
		value=. X
	case. dirSp do.
		value=. Sp
	case. dirAc do.
		value=. Ac
	end.
	value
)

reginM0=: dyad define
	direg=. 0{,x
	data=. y
	select. direg
	case. dirPc do.
NB.   		print data
		Pc=: data
NB.  		print Pc
	case. dirB do.
		B=: data
	case. dirX do.
		X=: data
	case. dirSp do.
		Sp=: data
	case. dirAc do.
		Ac=: data
	end.
)

spaceM0=: monad define
  NB. espacios de la M0
  NB. memoria
  memory=:?(memcap , word)$radix

  NB. almacenamiento de trabajo

  NB. - Registro Acumulador
  Ac=: ?word $ radix
  NB. - Registro Base
  B =: ?dir $ radix
  NB. - Registro Índice
  X =: ?dir $ radix
  NB. - Registro Puntero de Pila
  Sp=: ?dir $ radix

  NB. almacenamiento de control

  NB. -indicadores
  ind=: ?4$radix
  NB. -stop y wait
  stop=:?radix
  wait=:?radix
  NB. Puntero de instrucci'on de la M0-ext
  Pc=: ?dir$radix
  NB. input/output

)

nameM0=: monad define
  dirPc=:0
  dirB=:1
  dirX=:2
  dirSp=:3
  dirAc=:4
  1
)

controlM0=: monad define

  NB.M0 control allocation
  instructionM0 ''
  indicatorM0 ''
  statusM0 ''
  addressM0 ''
)

instructionM0=: monad define
  NB. M0 instruction allocation
  NB. operation specification
  Opcode=:3+i.5
  InDi  =:0

  NB. operand specification
  Address=:8+i.dir

  mode  =:1+i.2
  ext_m1=:8+i.2
  ext_m2=:8+i.3


NB.   rd    =:12+i.2
NB.   rf    =:14+i.2
  
  f_dirBase=:8+i.16
  f_rb     =:8
  f_desp15 =:9+i.15
  f_desp16 =:8+i.16
  f_desp10 =:14+i.10
  f_factor =:10+i.4
  f_rd     =:14+i.3
  f_rid    =:15+i.2
  f_rf     =:11+i.3
  f_rif    =:12+i.2
  f_srci   =:11
  f_dsti	=:14
  f_pp_id1 =:17+i.2
  f_pp_id2 =:19+i.2
  f_sz	=:0,21+i.3
  f_cond	=:i.3
  
  NB. mode specification

  					NB. 1 2
  cMabs1 	=:0			NB. 0 0
  cMinx  	=:1			NB. 0 1
  cMrel	=:2 			NB. 1 0

  cPrD	=:0
  cPoD	=:1
  cPrI	=:2
  cPoI	=:3

NB. constantes cond de los saltos

  cEQ=:1
  cNE=:5
  cMA=:2
  cMN=:7
  cMAE=:3
  cMNE=:6
  cNUN=:0
  cSIE=:4

NB. 	#define	cE	(0x1)
NB. 	#define	cNE	(0x5)
NB. 	#define	cG	(0x2)
NB. 	#define	cNG	(0x6)
NB. 	#define	cL	(0x7)
NB. 	#define	cNL	(0x3)
NB. 	#define cAw	(0x4)		/* Always */
NB. 	#define cNv	(0x0)		/* Never  */


NB.   f_MbInx =:8,9			NB. 8  9
  cMbInx =:0			NB. 0  0
NB.   f_r_r  =:8,9,10		NB. 8  9 10 11 12 13  14 15 16   17 18	19 20 21 22 23
  cr_r   =:2			NB. 0  1  0
  		  			NB. 0  1  0  1  0  0   0  r  r    0  0  0  0  0  0  0	Ac, [Ac|B|X|Sp]
  		  			NB. 0  1  0  0  r  r   0  r  r    0  0  0  0  0  0  0	[B|X|Sp|Pc], [Ac|B|X|Sp]
NB.   f_r_m  =:8,9,10		   
  cr_m   =:6  			NB. 1  1  0  1  0  0   0 ~0 ~0    0  0  0  0  0  0  0	Ac, @[B|X|Sp]
  		  			NB. 1  1  0  0  x  x   0 ~0 ~0    0  0  0  0  0  0  0	[B|X|Sp|Pc], @[B|X|Sp]
  		  			NB. 1  1  0  1  0  0   x ~0 ~0    0  0  x  x  0  0  1	Ac, [@][[+/-]([B|X|Sp])|([B|X|Sp])[+/-]]
  		  			NB. 1  1  0  0  x  x   x ~0 ~0    0  0  x  x  0  0  1	[B|X|Sp|Pc], [@][[+/-]([B|X|Sp])|([B|X|Sp])[+/-]]
  		  			NB. 1  1  0  1  0  0   1  0  0    0  0  1  1  0  0  1	Ac, >dir
  		  			NB. 1  1  0  0  x  x   1  0  0    0  0  1  1  0  0  1	[B|X|Sp|Pc], >dir

NB.   f_m_r  =:8,9,10		NB. 1  1  1 11 12 13  14 15 16   17 18	19 20 21 22 23
  cm_r   =:7			NB. 1  1  1  0 ~0 ~0   0  r  r    0  0  0  0  0  0  0	@[B|x|Sp], [Ac|B|X|Sp]
  		  			NB. 1  1  1  x ~0 ~0   0  r  r    x  x  0  0  0  0  1	[@][[+/-]([B|x|Sp])|([B|x|Sp])[+/-]], [Ac|B|X|Sp]
  		  			NB. 1  1  1  1  0  0   0  r  r    1  1  0  0  0  0  1	>dir, [Ac|B|X|Sp]

NB.   f_i_r  =:8,9,10		NB.         11 12 13  14 15 16   17 18	19 20 21 22 23
  ci_r   =:28			NB. 1  1  1  0  0  0   0  r  r    1  1	 0  0  0  0  1	inm,	[Ac|B|X|Sp]

NB.   f_i_m  =:8,9,10	 	NB. 
  ci_m   =:12  			NB. 0  1  1  0  0  0   0 ~0 ~0    1  1  0  0  0  0  1	inm,	@[B|X|Sp]
  		  			NB. 0  1  1  0  0  0   x ~0 ~0    1  1  x  x  0  0  1	inm,	[@][[+/-]([B|X|Sp])|([B|X|Sp])[+/-]]
  		  			NB. 0  1  1  0  0  0   1  0  0    1  1  1  1  0  0  1	inm,	>dir

  ci_src =:3		   	NB. 0  1  1
  ca_dst =:3		   	NB. 0  1  1

  NB. operaciones de registros y bifurcaciones
)

indicatorM0=: monad define
  1
)

NB.------------
NB.-- Sintax --
NB.------------

syntaxM0=: monad define
  NB. ;mapt;typet;x;Op                  NB. 0=0 1=1 2=x 3=Op
  NB. form inicializada vacia
  form=: 0 0 2 $ 0
  mapt=: 0 0 $ 0
  typet=: 0 $ 0
  x=.2
  Op=.3

  'Opcode'  insertfield Op
  'Address' insertfield x
  'mode'	 insertfield x
  'InDi'	 insertfield x

  fa InDi,mode,Opcode,Address  
  NB.fb InDi,0,0,Opcode,Address  

  orop =: _1}. +/\0,2^+/"1*./"1 form  NB.¯1↓ +\0,2*+/∧/form
  oplist=: 32 5$ 'CPMR CPRM NEG  ASR  ADC  SBB  AND  OR   NOT  XOR  SHL  SHR  LEA  LEAB LEAX LEASPCMP  ADD  SUB  INC  DEC  ROL  ROR  i    i    i    i    i    CALL JMP  JCONUJCONS'
)
NB. formato de instrucci'on a
fa=:monad define
  ptrn=.y
  maskp=. (msk 'InDi'),(msk 'mode'),(msk 'Opcode'),(msk 'Address')
  valuep=.(typ 'InDi'),(typ 'mode'),(typ 'Opcode'),(typ 'Address')
  w=.#maskp
  bptrn=.  2 2 #: (ptrn + (-.maskp) * w $ w){valuep,0,1 NB. ⍉ 2 2 ⊤ valuep[ptrn + (~maskp) × w ⍴ w]
  insertpattern bptrn
)


insertpattern=:monad define
  ptrn=.y NB.;widthf;lastp;w
  w=. #ptrn
  lastp=. 0 { $form
  widthf=. 1 { $form

select. ((widthf<w),(widthf>w),(widthf=w))#0 1 2
case. 0 do. NB. el tama~no del pattern es mayor que los almacenados en form
  form =:form ,"2 ((w-widthf) 2$ 1 0)            NB.((widthf ⍴ 1),(w-widthf)⍴0)\[1] form  expande el ancho del pattern en form
NB.   form[;widthf+⍳w-widthf;]← (lastp, (w-widthf),2) ⍴ 1 0  NB. rellena con 1 0 = 2
case. 1 do. NB. el tama~no del pattern es menor que los almacenados en form
NB.    ptrn ← ((w ⍴ 1), (widthf-w)⍴ 0)\[0]ptrn
NB.    ptrn[s+⍳widthf-w;]← ((widthf-w),2) ⍴ 1 0     NB. rellena con 1 0 = 2
  ptrn=. ptrn ,"2 ((widthf-w) 2 $ 1 0)
case. 2 do. NB. inserta el formato al final
end.
  form=: form , ptrn
   NB. form[lastp;;]←ptrn  
)

insertfield=:dyad define 
  name=.x
  type=.y
  w=. _1 {. $mapt
  l=. #name
  lastm=. 1 {. $mapt
  select. ((w<l),(w>l),(w=l))#0 1 2
case. 0 do. NB. la longitud del nombre es mayor que los almacenados en mapt
   mapt=: mapt ,"1 ((l-w)$ ' ')                   NB. expande el ancho de los nombres
case. 1 do. NB. la longitud del nombre es menor que los almacenados en mapt
   name=. name,(w-l)$' '
case. 2 do. NB. inserta el nombre al final
end.
   mapt=:  mapt , name
NB.   mapt[lastm;]←name
   typet=: typet , type  
)

typ=:monad define
  name=.y
  w=._1{. $mapt
  l=. ". '# ',name
  name=.name,(w-#name)$ ' '
  type=. l $ ((*./"1 name ="1 1 mapt) i. 1){ typet
)

msk=: monad define
 name=.y
 mask=. (". '# ',name)$ 1
)

NB.-------------------
NB.-- Status format --
NB.-------------------

statusM0=:monad define
  NB. estatus de la M0
  NB. control de modo
  NB. Conjunto de resgistros
  NB. prioridad de interrupci'on
  NB. modo trace
  NB. conditiones
  fZ=:0
  fN=:1
  fO=:2
  fC=:3
  Invop=:4
  NB. codificaci'on del modo
  Kernel=: 0
  Supervisor=: 1
  User=: 2
)


NB.---------------------------------
NB.-- Addressing in the  -M0 --
NB.---------------------------------


readM0=: monad define
  address=.y
  NB.  M0 read de registro, registropf o memoria
  size=.Size{address
  location=.(Value{address)
  select. Space{address NB. Branch acorde al espacio de trabajo
  case. ws do. NB. Registros
    data=. regoutM0 location
  case. memadr do. NB. Memoria
    data=.,(adrcap|location){memory
    NB. se recuperan los bits de la memoria especificados en location, con modulo memcap.
  end.
  data		NB. return value
)

writeM0=: dyad define
  address =. x
  data =. y
  NB.    M0 write de registro, registropf o memoria
  size=.Size{address
  location=.,(Value{address)

  select. Space{address
    case. ws do. NB. Acumulador
      (0{location) reginM0 (-size) {. ,data
    case. memadr do. NB. Write en memoria
      NB. if. -.$location do. location=.,location end.
      memory=: (word wide data) location}memory
  end.
)

NB.---------------------------
NB.-- Address Modification  --
NB.---------------------------

NB. Ejecutar antes la allocation
addressM0=: monad define
   NB. Attributes
   Size=:0
   Space=:1
   Value=:2
   NB. spaces name ?
   ws=:0
   memadr=:1
)

adrSrcM0=: monad define
  field=.y
  if. field=3 do.
	inst_mod=. fld ext_m1
	if. inst_mod=cMbInx do.
		address=. word,memadr,(magni regoutM0 dirB)+((magni regoutM0 dirX)*fld0 f_factor)+ fldOff f_desp10
		indirecto=. fld InDi
	else.
	  NB. two adrress 
		inst_ty=. fld ext_m2
		select. inst_ty
		case. cr_r do.
			indirecto=.0
			address=.(((fld f_rf)=dirAc){dir,word),ws, fld f_rf
		case. cr_m do.
			indirecto=.0
			address=.(((fld f_rf)=dirAc){dir,word),ws, fld f_rf
		case.	cm_r do.   NB. m_r o i_m
			indirecto=.fld f_srci
			r=. 5|fld f_rif
			sz=. radix | fld f_sz
NB. 			print sz
			op_sz=:sz
			pp=.fld f_pp_id1
NB. 			print 'Entro a M_r'
NB. 			print pp
			select. pp
			case. cPrD do.
				step=:-1
				ea=. (word * sz) pre_decM0 r
			case. cPrI do.
				step=:1
				ea=. (word * sz) pre_incM0 r
			case. cPoD do.
				step=:-1
				ea=. (word * sz) pos_decM0 r
			case. cPoI do.
				step=:1
				ea=. (word * sz) pos_incM0 r
NB. 				print ea
NB. 				print r
NB. 				print sz
			end.
			address=.ea	
		case.	ci_src do.
			indirecto=.0
			r=. dirPc
			sz=. 1
			address=.(word * sz) pos_incM0 r
		end.
  	end.
  else.
	select. field 
	NB. one address
  	case. cMabs1 do.
		address=. word,memadr,fld Address
	  case. cMinx do.
		address=. word, memadr, (magni regoutM0 dirX)+fld f_dirBase
	  case. cMrel do.
		offset=. fldOff f_desp15
		base=. magni regoutM0 (fld f_rb) { dirPc,dirB
		address=. word, memadr,(radix^dir)|base+offset
	end.
	indirecto=. fld InDi
  end.
  if. indirecto do.
NB. 	print address
	address=.word,memadr,(radix^dir)|magni readM0 address
NB. 	print address
  end.
  address
)

adrDstM0=: monad define
  field=.y
  if. field=3 do.
	inst_mod=. fld ext_m1
	if. inst_mod=cMbInx do.
		address=. word,ws,dirAc
		indirecto=.0
	else.
	  NB. two adrress 
		inst_ty=. fld ext_m2
		select. inst_ty
		case. cr_r do.
			indirecto=.0
			NB. address=.(((fld f_rd)=dirAc){dir,word),ws, fld f_rd (Considera el qie eñ reg dst es de 3 bits
			address=.(((fld0 f_rid)=dirAc){dir,word),ws, fld0 f_rid
		case. cm_r do.
			indirecto=.0
			address=.(((fld0 f_rid)=dirAc){dir,word),ws, fld0 f_rid
NB. 			print address
		case.	cr_m do.   NB. r_m
			indirecto=.fld f_dsti
			r=. fld f_rid
			op_sz=: sz=. radix | fld f_sz
			pp=.fld f_pp_id2
			select. pp
			case. cPrD do.
				step=:-1
				ea=. (word * sz) pre_decM0 r
			case. cPrI do.
				step=:1
				ea=. (word * sz) pre_incM0 r
			case. cPoD do.
				step=:-1
				ea=. (word * sz) pos_decM0 r
			case. cPoI do.
				step=:1
				ea=. (word * sz) pos_incM0 r
			end.
			address=.ea	
		case.	ca_dst do.
NB. 			indirecto=.1
NB. 			r=. dirPc
NB. 			sz=. 1
NB. 			address=.(word * sz) pos_incM0 r
			indirecto=.fld f_dsti
			r=. fld f_rid
			op_sz=: sz=. radix | fld f_sz
			pp=.fld f_pp_id2
			select. pp
			case. cPrD do.
				step=:-1
				ea=. (word * sz) pre_decM0 r
			case. cPrI do.
				step=:1
				ea=. (word * sz) pre_incM0 r
			case. cPoD do.
				step=:-1
				ea=. (word * sz) pos_decM0 r
			case. cPoI do.
				step=:1
				ea=. (word * sz) pos_incM0 r
			end.
			address=.ea	
		end.
  	end.
  else.
	address=. word,ws,dirAc
	indirecto=.0
  end.
  if. indirecto do.
NB.   print 'Destino'
NB.   print address
	address=.word,memadr,(radix^dir)|magni readM0 address
NB.   print address
  end.
  address
)


pos_incM0=: dyad define
  op_sz =. x
  size =. word
  r =. 0{,y
  NB. M0 post-increment
  address=. size,memadr,magni regoutM0 r
  adri=. (Value{address)+op_sz%word
  data=.dir magnr adri
NB.   print r
NB.       print adri
NB.   	 print data
NB.   print address
  r reginM0 data
  address
)

pre_incM0=: dyad define
  op_sz =. x
  size=.word
  r =. y
  NB. M0 pre-increment
  address=.(op_sz%word)+magni regoutM0 r
  r reginM0 dir magnr (radix^dir) | address 
  size,memadr,address
)

pre_decM0=:dyad define
  op_sz =. x
  size =. word
  r =. y
NB.   print x
NB.   print y
  NB. M0 pre-decrement
  adrd=.(magni regoutM0 r)-op_sz%word
  address=. size,memadr,adrcap|adrd
  r reginM0 dir magnr Value{address
  address
)

pos_decM0=:dyad define
  op_sz =. x
  size =. word
  r =. y
  NB. M0 pos-decrement
  address=. size,memadr,(magni regoutM0 r)
  adrd=. Value{address
  r reginM0 dir magnr adrcap|adrd-op_sz%word
  address
)


NB.------------------------
NB.-- Size specification -- 
NB.------------------------

sizeM0=: monad define
  NB. 0 operand size
  word
)

NB.----------------------
NB.-- Index Arithmetic --
NB.----------------------
incrM0=: monad define
  NB. incr Pc
  pci=.magni Pc
  Pc=:dir magnr memcap | 1+ pci
  pci
)
NB.------------------------------
NB.-- Integer Domain Signaling --
NB.------------------------------
getGtEqU=: monad define
	(-. (fC{ind) +. fZ{ind ),fZ{ind     NB. Carry=Borrow
)

getGtEqS=: monad define
	(-.((fZ{ind) +. -.(fN{ind) = fO{ind)),fZ{ind
)

signalM0NZ=: monad define
  res=. ,y
  
NB.    M0 numeric result
  ind=:((0{res){0 1) fN} ind 
  ind=:((-. +./ res){0 1) fZ} ind
)

signalM0NZO=: monad define
  res=. ,y
  NB. DEC PDP11 arithmetic result
  ind=:(0{res) fN} ind 
  ind=:(-. +./ res) fZ} ind
  ind=:(xmax +. xmin) fO} ind 
)

NB.----------------------------
NB.-- Floating-point numbers --
NB.----------------------------

flM0=: monad define
)


flM0i=: monad define
)

flM0r=: dyad define
)


NB.-- floating-point domain signaling --

signalM0FNZ=: monad define
)

signalM0FNZO=: monad define
)

NB.------------------------------------
NB.-- Data Manipulation Instructions --
NB.------------------------------------
 
CPMR=: monad define
  NB. M0 Load Ac from Mem
  mod=: fld mode
  dirfte=: adrSrcM0 mod
  dest=:adrDstM0 mod
  od=.readM0 dirfte
  dest writeM0 od
  signalM0NZ od
)


CPRM=: monad define
  NB. M0 Load Ac from Mem
  mod=. fld mode
  m1=.fld ext_m1
  if. (3=mod) *. -. cMbInx=m1 do.
	dest=: adrSrcM0 mod
  	dirfte=:adrDstM0 mod
  else.
	dest=: adrSrcM0 mod
	dirfte=:adrDstM0 mod
  end.
  od=.readM0 dirfte
  dest writeM0 od
  signalM0NZ od
)

NB. ST=: monad define
NB.   NB. M0 Store Ac in Mem 
NB.   dest=.word adrM0 Address
NB.   dest writeM0 Ac
NB. )

NB.--------------------------------
NB.--    Logical Instructions    --
NB.--------------------------------

NB. AND  OR   NOT  XOR  SHL  SHR  

AND=: monad define
  NB. M0 AND
  mod=: fld mode
  dirfte=: adrSrcM0 mod
  dest=:adrDstM0 mod
  od1=.readM0 dirfte
  od2=.readM0 dest
  result=.od2 *. od1
  dest writeM0 result
  signalM0NZ result
)

OR=: monad define
  NB. M0 OR
  mod=: fld mode
  dirfte=: adrSrcM0 mod
  dest=:adrDstM0 mod
  od1=.readM0 dirfte
  od2=.readM0 dest
  result=.od2 +. od1
  dest writeM0 result
  signalM0NZ result
)

NOT=: monad define
  NB. M0 NOT
  mod=: fld mode
  dirfte=: adrSrcM0 mod
  dest=:adrDstM0 mod
  od1=.readM0 dirfte
  result=.-.od1
  dirfte writeM0 result
  signalM0NZ result
)

XOR=: monad define
  NB. ≠ is XOR
  mod=: fld mode
  dirfte=: adrSrcM0 mod
  dest=:adrDstM0 mod
  od1=.readM0 dirfte
  od2=.readM0 dest
  result=.-.od1 = od2
  dest writeM0 result
  signalM0NZ result
)

SHL=: monad define
  NB. M0 Logical Shift left
  mod=: fld mode
  dirfte=: adrSrcM0 mod
  dest=:adrDstM0 mod
  sz=.Size{dest
  od1=.readM0 dirfte
  od2=.readM0 dest
  value=.magni od2
  result=.value*radix^sz <. magni od1
  ind=:((result>_1+radix^sz){ 0 1) fC} ind
  rl=. , sz magnr <.result  NB. <. es el piso
  dest writeM0 rl
  signalM0NZ rl
)

SHR=: monad define
  NB. M0 Logical Shift right
  mod=: fld mode
  dirfte=: adrSrcM0 mod
  dest=:adrDstM0 mod
  sz=.Size{dest
  od1=.readM0 dirfte
  od2=.readM0 dest
  value=.magni od2
  result=.value%radix^ sz <. magni od1
  ind=:((radix | value){ 0 1) fC} ind
  rl=. ,sz magnr <.result  NB. <. es el piso
  dest writeM0 rl
  signalM0NZ rl
)

ROL=: monad define
  NB. M0 Logical Shift left
  mod=: fld mode
  dirfte=: adrSrcM0 mod
  dest=:adrDstM0 mod
  sz=:Size{dest
  od1=:readM0 dirfte
  od2=:readM0 dest
  value=:magni od2
  rot=:sz|magni od1
NB.   ind=:".": ind
  low =: (radix*(radix^sz-rot)|value)+fC{ind
NB.   if. ((3!:0)"0 low)=8 do.
NB. 	print 'low es flotante'
NB.   end.
  high=: <. value%radix^sz-rot
  result=: (low * radix^_1+rot)+ <. high%radix
NB.   if. *./ ((3!:0)"0 ind)=8 8 8 8 do.
NB. 	print 'indicador flotante antes'
NB.   end.
  ind=:((radix|high){0 1) fC} ind
NB.   if. *./ ((3!:0)"0 ind)=8 8 8 8 do.
NB. 	print 'indicador flotante despues =:'
NB.   end.
  rl=:,sz magnr <.result  NB. <. es el piso
  dest writeM0 rl
  signalM0NZ rl
NB.   if. *./ ((3!:0)"0 ind)=8 8 8 8 do.
NB. 	print 'indicador flotante despues signal'
NB.   end.
)

ROR=: monad define
  NB. M0 Logical Shift right
  mod=: fld mode
  dirfte=: adrSrcM0 mod
  dest=:adrDstM0 mod
  sz=.Size{dest
  od1=.readM0 dirfte
  od2=.readM0 dest
  rot=:sz|magni od1
  value=: magni od2
  high=: (radix^rot)|value
  low=: <.value%radix^rot
  result=:((radix^sz-rot)*(fC{ind)+high*radix) + <. low
  ind=:(<. result %radix^sz) fC} ind
  rl=: sz magnr <.(radix^sz)|result  NB. <. es el piso
  dest writeM0 rl
NB.   print 'ind antes'
NB.   print (3!:0)"0 ind
  signalM0NZ rl
NB.   print 'ind despues signal'
NB.   print (3!:0)"0 ind
)

NB.-------------------------------
NB.-- Arithmetical Instructions --
NB.-------------------------------

NB. NEG  ASR  ADC  SBB  
NB. ADD  SUB  INC  DEC  i    i    i    
NB. CMP  

NEG=: monad define
	NB. M0 radix complement

  mod=: fld mode
  dirfte=:adrSrcM0 mod
  dest=. adrDstM0 mod
  od=.readM0 dirfte
  value=.radixcompr od
  result=.-value
  rl=. ,word radixcompr result  NB. <. es el piso
  dirfte writeM0 rl
  signalM0NZO 	
)
 
ASR=: monad define
  NB. M0 Shift Arithmetic
  mod=: fld mode
  dirfte=:adrSrcM0 mod

  dest=: adrDstM0 mod
  od=.readM0 dirfte
  sz=.Size{dest
  od1=.readM0 dirfte
  od2=.readM0 dest
  value=.radixcompi od1
  result=.value%radix^ sz <. magni od1
  ind=:((radix | value){ 0 1) fC} ind
  rl=. ,sz radixcompr <.result  NB. <. es el piso
  dest writeM0 rl
  signalM0NZ rl

  cy=. radix | >. result*radix
  ind=: cy fC}ind
)

ADC=: monad define
  NB. ADD de  M0
  mod=: fld mode
  dirfte=:adrSrcM0 mod
  ad=: readM0 dirfte
  NB. ad has word bits from "Space[Value]"
  addend=: radixcompi ad
  NB. Interpreted bits as radix complement
  dest=: adrDstM0 mod
  augend=: radixcompi readM0 dest
  sum=: augend+addend+fC{ind
  NB. APL Add
  rl=:,word radixcompr sum
  NB. sum representation as word in rl 
  dest writeM0 rl
  NB. write in dest the representation
  signalM0NZ rl
  NB. Flag checks
  cy=. (Size{dest) carryfrom augend,addend,fC{ind
  ind=: cy fC}ind

)

SBB=: monad define
  NB. SUB de M0
  mod=: fld mode
  dirfte=:adrSrcM0 mod

  dest=: adrDstM0 mod
  ad=.readM0 dirfte

  NB. ad has word bits from "Space[Value]"
  addend=. radixcompi ad
  NB. Interpreted bits as radix complement
  augend=. radixcompi readM0 dest
  sum=. augend-addend-fC{ind
  NB. APL Add
  rl=. ,word radixcompr sum
  NB. sum representation as word in rl 
  dest writeM0 rl
  NB. write in dest the representation
  signalM0NZ rl
  NB. Flag checks
  cy=.-. (Size{dest) carryfrom augend,((_1+radix^(Size{dest))-addend-fC{ind),1
  ind=:cy fC} ind
)

ADD=: monad define
  NB. ADD de  M0
  mod=: fld mode
  dirfte=:adrSrcM0 mod
  ad=: readM0 dirfte
  NB. ad has word bits from "Space[Value]"
  addend=: radixcompi ad
  NB. Interpreted bits as radix complement
  dest=: adrDstM0 mod
  augend=: radixcompi readM0 dest
  sum=: augend+addend
  NB. APL Add
  rl=: ,word radixcompr sum
  NB. sum representation as word in rl 
  dest writeM0 rl
  NB. write in dest the representation
  signalM0NZ rl
  NB. Flag checks
  cy=. (Size{dest) carryfrom augend,addend
  ind=: cy fC}ind
)

INC=: monad define
  NB.   M0 M0 Count Decrement
  mod=: fld mode
  dirfte=:adrSrcM0 mod

  dest=: adrDstM0 mod
  od=.readM0 dirfte
  value=.radixcompi od
  result=.value+1
  rl=.word radixcompr <.result  NB. <. es el piso
  dirfte writeM0 rl
  signalM0NZ rl
)

SUB=: monad define
  NB. SUB de M0
  mod=: fld mode
  dirfte=:adrSrcM0 mod

  dest=: adrDstM0 mod
  ad=.readM0 dirfte

  NB. ad has word bits from "Space[Value]"
  addend=. radixcompi ad
  NB. Interpreted bits as radix complement
  augend=. ,radixcompi readM0 dest
  sum=. augend-addend
  NB. APL Add
  rl=.word radixcompr sum
  NB. sum representation as word in rl 
  dest writeM0 rl
  NB. write in dest the representation
  signalM0NZ rl
  NB. Flag checks
  cy=.-. (Size{dest) carryfrom augend,((_1+radix^(Size{dest))-addend),1
  ind=:cy fC} ind
)

DEC =: monad define
  NB.   M0 M0 Count Decrement
  mod=: fld mode
  dirfte=:adrSrcM0 mod

  dest=: adrDstM0 mod
  od=.readM0 dirfte
  value=.radixcompi od
  result=.value-1
  rl=.word radixcompr <.result  NB. <. es el piso
  dirfte writeM0 rl
  print ind
  signalM0NZ rl
  print ind
)

CMP=: monad define
  NB. CMP de M0
  mod=: fld mode
  dirfte=:adrSrcM0 mod

  dest=: adrDstM0 mod
  ad=.readM0 dirfte

  NB. ad has word bits from "Space[Value]"
  addend=. radixcompi ad
  NB. Interpreted bits as radix complement
  augend=. radixcompi readM0 dest
  sum=. augend-addend
  NB. Substrac
  rl=.word radixcompr sum
  NB. write in dest the representation
  signalM0NZO rl
  NB. Flag checks
  cy=. -.(Size{dest) carryfrom augend,((_1+radix^word)-addend),1
  ind=:,(cy{0 1) fC} ind  
)

NB.--------------------------------
NB.-- Adress Instruction 		--
NB.--------------------------------

NB. LEA  LEAB LEAX LEASP
LEA=: monad define

  mod=: fld mode
  dirfte=: adrSrcM0 mod
  dest=:adrDstM0 mod
  od=. (Size{dest) magnr (radix^dir)|Value{dirfte
  dest writeM0 od

)

LEAB=: monad define
NB.   print 'LEAB  !!!!!!!!!!!!!!!' 
  mod=: fld mode
  dirfte=: adrSrcM0 mod
  dest=: dir,ws,dirB
  od=:dir magnr (radix^dir)|Value{dirfte
  dest writeM0 od
)

LEAX=: monad define

  mod=: fld mode
  dirfte=: adrSrcM0 mod
  dest=: dir,ws,dirX
  od=:dir magnr (radix^dir)|Value{dirfte
  dest writeM0 od

)

LEASP=: monad define

  mod=: fld mode
  dirfte=: adrSrcM0 mod
  dest=: dir,ws,dirSp
  od=:dir magnr (radix^dir)|Value{dirfte
  dest writeM0 od
)

NB.--------------------------------
NB.-- Floating-point Instruction --
NB.--------------------------------


NB.----------------------------
NB.-- Instruction Sequencing --
NB.----------------------------
NB. i    i    i    i    i    JMP  
NB. JCONUJCONS

CALL=: monad define
NB.   mod=: fld mode 
NB.   dest=: adrSrcM0 mod
  dest=: (magni regoutM0 dirPc) + fldOff f_desp16
  (word pre_decM0 dirSp) writeM0 word magnr magni regoutM0 dirPc
  dirPc reginM0 dir magnr dest
)

JMP=: monad define
  mod=: fld mode 
  dest=: adrSrcM0 mod
  dirPc reginM0 dir magnr Value{dest
)

NB. JEQ=: monad define
NB.   dest=: (magni regoutM0 dirPc) + fldOff f_desp16
NB.   me=.getGtEqS ''
NB.   cnd=: f_cond { inst
NB.   c=: -. (0{cnd)=+./me *. (1+i.2){cnd
NB.   if. c=1 do.
NB.   NB. Saltar
NB.      dirPc reginM0 dir magnr dest
NB.   end.
NB. )
NB.
NB. JNE=: monad define
NB.   dest=: (magni regoutM0 dirPc) + fldOff f_desp16
NB.   me=.getGtEqS ''
NB.   cnd=: f_cond { inst
NB.   c=: -. (0{cnd)=+./me *. (1+i.2){cnd
NB.   if. c=1 do.
NB.   NB. Saltar
NB.      dirPc reginM0 dir magnr dest
NB.   end.
NB. )
NB.
JCONS=: monad define
  dest=: (magni regoutM0 dirPc) + fldOff f_desp16
  me=.getGtEqS ''
  cnd=: f_cond { inst
  c=: -. (0{cnd)=+./me *. (1+i.2){cnd
  if. c=1 do.
  NB. Saltar
     dirPc reginM0 dir magnr dest
  end.
)

JCONU=: monad define
  dest=: (magni regoutM0 dirPc) + fldOff f_desp16
  me=.getGtEqU ''
  cnd=: f_cond { inst
  c=: -. (0{cnd)=+./me *. (1+i.2){cnd
NB.   print 'cond sin signo'
NB.   print c
  if. c=1 do.
     dirPc reginM0 dir magnr dest
  end.
)

cycleM0=: monad define
  NB. basic cycle of    M0
  whilst. -. stop do.       NB. do <sents> while <cond> end.
    interruptM0
    execute ifetchM0 ''
  end.
)

ifetchM0=: monad define
  NB.    M0 instruction fetch
  inst=.readM0 word, memadr, incrM0 Pc
)

NB.-----------------
NB.-- Supervision --
NB.-----------------
NB.
NB. NB.--------------------
NB. NB.-- Input / Output --
NB. NB.--------------------

NB. ----------------------
NB. --     Testing      --
NB. ----------------------

NB. Start  M0, Pc=.1050

initiateM0 ''
syntaxM0 ''

NB. @Test: ADD - inmediate
test_ld=: monad define
  NB. Load instrucction   LD  0008
  (word, memadr, magni Pc) writeM0 0 0 0 0 0 0 0 0  0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0
  NB. Set Ac -1
  (word, ws, 0) writeM0 (word radixcompr _1)
  NB. Set Mem[0008] to 5
  (word, memadr, 8) writeM0 (word radixcompr 5)
  NB. Load and execute instrucction from Pc
  inst=: ifetchM0 ''
  execute inst
  NB. Assert equals
  5 = magni readM0 (word, ws, 0)
)

test_st=: monad define
  NB. Load instrucction   LD  0008
  (word, memadr, magni Pc) writeM0 0 0 0 0 0 0 0 1  0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0
  NB. Set Ac -1
  (word, ws, 0) writeM0 (word radixcompr _1)
  NB. Load and execute instrucction from Pc
  inst=: ifetchM0 ''
  execute inst
  NB. Assert equals
  _1 = radixcompi readM0 (word, memadr, 8)
)

cargar =: monad define
  f=.readfile <y
  f=.(_1}.f),'  ',((word*2)$'0 '),LF
  long=.(dir*2)+2+(word*2)+1
  filas=. ($f)%long
  last =. filas-1
  cod=. ". _1}."1 (filas,long) $ f
  dirs=. magni (<(i.last);i.dir) { cod
  cont=. (<(i.last);dir+i.word) { cod
  memory=: cont dirs} memory
  Pc =: (i.dir) { ,last { cod
)

info_registers=: monad define
NB.       print ind
NB. 	print $ind
NB. 	print ind # 'ZNVC'
	r_name=: (6, 4) $'Pc  B   X   Sp  Ac  Ind '
      l=.5
	i_magni=:(6,10)$(10 ": (magni (4,16)$ Pc,B,X,Sp),(magni Ac)),(_10{.ind # 'ZNVC')
	i_radix=:(6,10)$(10 ": (radixcompi (4,16)$ Pc,B,X,Sp),(radixcompi Ac)),'        '
	i_hex=:(magni (4,16)$ Pc,B,X,Sp),(magni Ac)
      logs=: 4 4 4 4 6
      i_hex=:(6,9)$(,((5,3)$' 0x') ,. ({&'0123456789abcdef'@>)"0 (logs (<@$"0 0) 16) ((>@[ <@#: ])"(0,0)) i_hex),'         '
      r_name,.i_magni,.i_radix,.i_hex
)

NB. examine=: monad define
NB.       dirs=. ,y
NB.       l=:#dirs
NB.       logs=. l$4
NB. 	zcont=.l$6
NB. 	cont=.dirs{memory
NB. 	r_dirs=. ((l,3)$' 0x'),. >(<@{&'0123456789abcdef')&> ((l$4) (<@$"0 0) 16) (<@#:&>)"(0,0) dirs
NB.
NB. 	d_magni=.(l,10)$10 ": magni cont
NB. 	d_radix=.(l,10)$10 ": radixcompi cont
NB. 	d_hex=.((l,3)$' 0x') ,. (({&'0123456789abcdef'@>)"0 (zcont (<@$"0 0) 16) ((>@[ <@#: ])"(0,0)) magni cont)
NB. 	d_str=.(l,3)$,(magni"1 (l,3,8) $ ,cont)
NB.       d_msk=.((>&127) +. <&32)"0 d_str
NB. 	d_char=.' ',.((d_msk*46)+(-.d_msk)*d_str)({"0 1) a.
NB. 	r_dirs,.(10 (":"0) dirs),.((l,3)$' | '),.d_magni,.d_radix,.d_hex,.d_char
NB. )

examine=: monad define
      dirs=. (2^dir)|,y
      l=:#dirs
      logs=. l$4
	zcont=.l$6
	cont=.dirs{memory
	r_dirs=. ((l,3)$' 0x'),. >(<@{&'0123456789abcdef')&> ((l$4) (<@$"0 0) 16) (<@#:&>)"(0,0) dirs
	d_magni=.(l,10)$10 ": magni cont
	d_radix=.(l,10)$10 ": radixcompi cont
	d_hex=.((l,3)$' 0x'),.((6$16)#:magni cont)    geta"1 1 (l,16)$'0123456789abcdef'
	d_str=.(l,3)$,(magni"1 (l,3,8) $ ,cont)
	d_msk=.((>&127) +. <&32)"0 d_str
	d_char=.' ',.((d_msk*46)+(-.d_msk)*d_str)({"0 1) a.
	r_dirs,.(10 (":"0) dirs),.((l,3)$' | '),.d_magni,.d_radix,.d_hex,.d_char
)

geta=: dyad define
	x{y
)

NB. stepi=: monad define
NB. 	execute ifetch ''
NB. )

set_reg=: dyad define
NB.      dirs:=(,x),(5-#,x)$_1{,x
	x =.,x
	y =.,y
	dirReg=:(/:x){x
      l=:#dirReg
      sizes=:((i.5) e. dirReg) # |.word,4$dir
      values=:(/:x){l$y,(l-#y)$_1{y
      sgn=:* values
	for_i. i.#dirReg do.
		(i{dirReg) reginM0 0 ".,((1,12)$ 12": i{sizes), ((i{sgn){ (3, 12) $' magnr       magnr       radixcompr '), (1,12)$ 12 ": i{values
	end.
	info_registers ''
)

trim_all=: monad define
	p=.(-.*./\ (' ' = y))
	s=.(-.*./\. (' ' = y))

	((s*.p) # y)
)

set_mem=:dyad define
	x =. ,x
	y =. ,y
      l=:#x
NB.      sizes=:l$word
      values=: l$y,(l-l<.#y)$_1{y
      sgn=:* values
	for_i. i.#x do.
		(word, memadr, i{x) writeM0 ". ('(word ',((i{sgn){(3,12)$' magnr       magnr       radixcompr '),":(i{values)),' )'
NB. 0 ".,((1,12)$ ' word       '),((i{sgn){ (3, 12) $' magnr       magnr       radixcompr '), (1,12)$ 12 ": i{values
	end.
     x { memory
)

stepi=:monad define
      n=.(1<.#y){1,0{,y
	for_i. i.n do. execute ifetchM0 '' end.
	print info_registers ''
	print examine (magni Sp)+i.8
	3 disassembly magni Pc
)

disassi=:monad define
	dir=. 0{,y
      inst_bck=.inst
	inst=: dir{memory
	d_hex=.((4$16)#:plc){'0123456789abcdef'
	COp=.fld Opcode
	linea=. '##############'

	if. COp e. 30 31 do.
           su=.(7{inst){'U '
		Off=.radixcompi Address{inst
		tabla=.(8,4)$'NV  E   G',su,'  NL',su,' AW  NE  NG',su,' L',su,'  '
		linea=.,szline{.(_6{.":plc),' 0x',d_hex,'    ','J',((magni (i.3){inst) { tabla),'  PCR:', ": Off
		plc=:plc+1
	elseif. COp=28 do.
		Off=.radixcompi Address{inst
		linea=.,szline{.(_6{.":plc),' 0x',d_hex,'    ','CALL   PCR:', ": Off
		plc=:plc+1
	elseif. COp e. 24+i.4 do.
		linea=.,szline{.(_6{.":plc),' 0x',d_hex,'    i          '
		plc=:plc+1
	elseif. COp=COp do.
		szi=.0
		select. fld mode
		case. 0 do.
	           if. COp<2 do. 
				c=. COp{ 2 5$'LD   ST   '
			else.
				c=.COp{oplist
			end.
			adr=.((0{inst){(0{a.),'@'),'>',": fld Address
		case. 1 do.
	           if. COp<2 do. 
				c=. COp{ 2 5$'LD   ST   '
			else.
				c=.COp{oplist
			end.
			adr=.((0{inst){(0{a.),'@'),(": fld Address),'[X]'
		case. 2 do.
	           if. COp<2 do. 
				c=. COp{ 2 5$'LD   ST   '
			else.
				c=.COp{oplist
			end.
			adr=.((0{inst){(0{a.),'@'),((8{inst){2 4$'PCR:B-> '),": radixcompi f_desp15{inst
		case. 3 do.
	           if. COp<2 do. 
				c=.(2 <. COp+(fld ext_m1)){ 3 5$'LD   ST   CP   '
			else.
				c=.COp{oplist
			end.
			if. cMbInx=fld ext_m1 do.
				adr=. ((fld InDi){(0{a.),'@'),'B[X*',(": fld0 f_factor),'].', ": fldOff f_desp10
			else.
			NB. two adrress 
NB.                       print 'two address'
				inst_ty=. fld ext_m2
				select. inst_ty
				case. cr_r do.
					indf=.0	NB.fld f_srci
					rf=. (fld f_rf){8 2$'PcB X SpAc? ? ? '
					rf=. trim_all (c e. 4 5$ 'INC  DEC  NOT  NEG  '){(2,3)$rf,'    '
					indd=.0
					rd=. (fld f_rid){4 2$'AcB X Sp'
					if. (*./rd='Ac') do.
						ea=. trim_all rf
					else.
                 					ea=. trim_all rf,',',(trim_all rd)
					end.
				case. cr_m do. 
					indd=.fld f_dsti
					rd=. trim_all (fld f_rid){4 2$'? B X Sp'
					pp=.fld f_pp_id2
					select. pp
					case. cPrD do.
						ea=. (indd{(0{a.),'@'),(trim_all (radix | fld f_sz){' -'),'(',(trim_all rd),')'
						sz=.radix | fld f_sz
						ea=. trim_all (indd{(0{a.),'@'),(sz{'@-'),trim_all (sz { ' ('),(trim_all rd),trim_all sz{ ' )'
					case. cPrI do.
						ea=. (indd{(0{a.),'@'),(radix | fld f_sz){ (2,5)$'@ ',rd,' ', '+(',rd,')'
						sz=.radix | fld f_sz
						ea=. trim_all (indd{(0{a.),'@'),(sz{'@+'),trim_all (sz { ' ('),(trim_all rd),trim_all sz{ ' )'
					case. cPoD do.
						ea=. (indd{(0{a.),'@'),'(',rd,')',(radix | fld f_sz){' -'
						sz=.radix | fld f_sz
						ea=. trim_all(indd{(0{a.),'@'),trim_all (sz{'@ '),trim_all (sz { ' ('),(trim_all rd),trim_all sz{ (2,2)$'  )-'
					case. cPoI do.
						if. 0=fld f_rid do.
							szi=.szi+1
							dir1=. magni (plc+szi){memory
							ea=. trim_all (indd{'?>'),": dir1
						else.
							ea=. (indd{(0{a.),'@'),(radix | fld f_sz){ (2,5)$'@ ',rd,' ', '(',rd,')+'
							sz=.radix | fld f_sz
							ea=. trim_all (indd{(0{a.),'@'),trim_all (sz{'@ '),trim_all (sz { ' ('),(trim_all rd),trim_all trim_all sz{ (2,2)$'  )+'
						end.
					end.
					rf=.((fld f_rf){5 2$'PcB X SpAc')
					rf=.trim_all (c e. 4 5$ 'INC  DEC  NOT  NEG  '){(2,3)$rf,',','   '
					ea=. (trim_all rf),ea
				case.	cm_r do.   NB. m_r o i_m
					indf=.fld f_srci
					rf=. (5|fld f_rif){4 2$'? B X Sp'
					rf=.trim_all (c e. 4 5$ 'INC  DEC  NOT  NEG  '){(2,3)$rf,'  '
					pp=.fld f_pp_id1
					select. pp
					case. cPrD do.
NB.						print 'PREDEC'
						sz=.radix | fld f_sz
						ea=. trim_all (indf{(0{a.),'@'),(sz{'@-'),trim_all (sz { ' ('),(trim_all rf),trim_all sz{ ' )'
					case. cPrI do.
NB.						print 'PREINC'
						ea=. (indf{(0{a.),'@'),((radix | fld f_sz){' +'),'(',(trim_all rf),')'
						sz=.radix | fld f_sz
						ea=. trim_all (indf{(0{a.),'@'),(sz{'@+'),trim_all (sz { ' ('),(trim_all rf),trim_all sz{ ' )'
					case. cPoD do.
NB.						print 'POSDEC'
						ea=. (indf{(0{a.),'@'),'(',rf,')',(radix | fld f_sz){' -'
						sz=.radix | fld f_sz
						ea=. trim_all (indf{(0{a.),'@'),trim_all (sz{'@ '),trim_all (sz { ' ('),(trim_all rf),trim_all sz{ (2,2)$'  )-'
					case. cPoI do.
NB.						print 'POSINC'
						if. 0=fld f_rif do.
							szi=.szi+1
							adr1=. magni (plc+szi){memory
							ea=. trim_all (indf{'$>'),(": adr1)
						else.
							ea=. (indf{(0{a.),'@'),'(',(trim_all rf),')',(radix | fld f_sz){' +'
							sz=.radix | fld f_sz
							ea=. trim_all (indf{(0{a.),'@'),trim_all (sz{'@ '),trim_all (sz { ' ('),(trim_all rf),trim_all sz{ (2,2)$'  )+'
						end.
					end.
					rd =.(fld f_rid){4 2$'  B X Sp'
					if. (-. *./rd='  ')*.-. (COp{oplist) e. 9 5$ 'INC  DEC  NOT  NEG  LEAB LEAX LEASPLEA  JMP  ' do.
						ea=. (trim_all ea) , ',',trim_all rd					
					end.
					ea=. trim_all ea
				case.	ci_src do.
					indf=.fld f_dsti
					rf=. 5|fld f_rif
					rd=. trim_all (fld f_rid){4 2$'AcB X Sp'
					szi=.1
					dato1=.trim_all (rf=0){(2, 10)$ '??????????','$0x',((6$16)#:magni (plc+szi){memory){'0123456789abcdef'
					pp=.fld f_pp_id2
					select. pp
					case. cPrD do.
						ea=. (indf{(0{a.),'@'),((radix | fld f_sz){' -'),'(',rd,')'
						sz=.radix | fld f_sz
						ea=. trim_all (indf{(0{a.),'@'),(sz{'@-'),trim_all (sz { ' ('),(trim_all rd),trim_all sz{ ' )'
					case. cPrI do.
						ea=. (indf{(0{a.),'@'),((radix | fld f_sz){' +'),'(',rd,')'
						sz=.radix | fld f_sz
						ea=. (indf{(0{a.),'@'),(sz{'@+'),(sz { ' ('),(trim_all rd),sz{ ' )'
					case. cPoD do.
						ea=. (indf{(0{a.),'@'),'(',(trim_all rd),')',(radix | fld f_sz){' -'
						sz=.radix | fld f_sz
						ea=. trim_all (indf{(0{a.),'@'),trim_all (sz{'@ '),trim_all (sz { ' ('),(trim_all rd),sz{ (2,2)$'  )-'
					case. cPoI do.
						if. 0=fld f_rid do.
							szi=.szi+1
							dir1=. magni (plc+szi){memory
							ea=. trim_all (indf { '?>'), ": dir1
						else.
							ea=. (indf{(0{a.),'@'),'(',(trim_all rd),')',(radix | fld f_sz){' +'
							sz=.radix | fld f_sz
							ea=. trim_all (indf{(0{a.),'@'),trim_all (sz{'@ '),trim_all (sz { ' ('),(trim_all rd),trim_all sz{ (2,2)$'  )+'
						end.
					end.
					ea=.(trim_all dato1),',',ea
				case.  do.
					ea=.'?' 
				end.
				adr=.ea
			end.
		end.
		linea=.,szline{.(_6{.":plc),' 0x',d_hex,'    ',c,'  ',adr
		plc=:plc+1+szi
	end.
	inst=:inst_bck
	linea
)

disassembly=: dyad define
        inicio=.0{,y
	   l=.0{,x
	   szline=: 50
	plc=:inicio
	lst=. (0,szline)$' '
	for_i. inicio+i.l do.
NB. 		print 'i=',":i
		lst=. lst , disassi plc
	end.
	lst		
)