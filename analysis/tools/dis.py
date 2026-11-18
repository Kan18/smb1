"""A small 6502 disassembler for the ROM's PRG. usage: dis.py FROM TO, in hex."""
import sys
import os
rom=open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','..','Super Mario Bros. (World).nes'),'rb').read()[16:]
modes={'imp':0,'imm':1,'zp':1,'zpx':1,'zpy':1,'abs':2,'abx':2,'aby':2,'ind':2,'izx':1,'izy':1,'rel':1,'acc':0}
T={}
def add(n,l):
    for op,m in l: T[op]=(n,m)
for n,b in [('ora',0),('and',0x20),('eor',0x40),('adc',0x60),('lda',0xa0),('cmp',0xc0),('sbc',0xe0)]:
    add(n,[(b+9,'imm'),(b+5,'zp'),(b+0x15,'zpx'),(b+0xd,'abs'),(b+0x1d,'abx'),(b+0x19,'aby'),(b+1,'izx'),(b+0x11,'izy')])
add('sta',[(0x85,'zp'),(0x95,'zpx'),(0x8d,'abs'),(0x9d,'abx'),(0x99,'aby'),(0x81,'izx'),(0x91,'izy')])
for n,b in [('asl',0),('rol',0x20),('lsr',0x40),('ror',0x60)]: add(n,[(b+0xa,'acc'),(b+6,'zp'),(b+0x16,'zpx'),(b+0xe,'abs'),(b+0x1e,'abx')])
for n,o in [('bpl',0x10),('bmi',0x30),('bvc',0x50),('bvs',0x70),('bcc',0x90),('bcs',0xb0),('bne',0xd0),('beq',0xf0)]: add(n,[(o,'rel')])
add('bit',[(0x24,'zp'),(0x2c,'abs')]); add('cpx',[(0xe0,'imm'),(0xe4,'zp'),(0xec,'abs')]); add('cpy',[(0xc0,'imm'),(0xc4,'zp'),(0xcc,'abs')])
add('dec',[(0xc6,'zp'),(0xd6,'zpx'),(0xce,'abs'),(0xde,'abx')]); add('inc',[(0xe6,'zp'),(0xf6,'zpx'),(0xee,'abs'),(0xfe,'abx')])
add('ldx',[(0xa2,'imm'),(0xa6,'zp'),(0xb6,'zpy'),(0xae,'abs'),(0xbe,'aby')]); add('ldy',[(0xa0,'imm'),(0xa4,'zp'),(0xb4,'zpx'),(0xac,'abs'),(0xbc,'abx')])
add('stx',[(0x86,'zp'),(0x96,'zpy'),(0x8e,'abs')]); add('sty',[(0x84,'zp'),(0x94,'zpx'),(0x8c,'abs')]); add('jmp',[(0x4c,'abs'),(0x6c,'ind')]); add('jsr',[(0x20,'abs')])
for n,o in [('brk',0),('php',8),('clc',0x18),('plp',0x28),('sec',0x38),('rti',0x40),('pha',0x48),('cli',0x58),('rts',0x60),('pla',0x68),('sei',0x78),('dey',0x88),('txa',0x8a),('tya',0x98),('txs',0x9a),('tay',0xa8),('tax',0xaa),('clv',0xb8),('tsx',0xba),('iny',0xc8),('dex',0xca),('cld',0xd8),('inx',0xe8),('nop',0xea),('sed',0xf8)]: add(n,[(o,'imp')])
a=int(sys.argv[1],16); end=int(sys.argv[2],16)
while a<end:
    b=rom[a-0x8000]; n,m=T.get(b,('???','imp')); l=modes[m]
    v=int.from_bytes(rom[a-0x8000+1:a-0x8000+1+l],'little') if l else 0
    s={'imp':'','acc':'','imm':f'#${v:02x}','zp':f'${v:02x}','zpx':f'${v:02x},x','zpy':f'${v:02x},y','abs':f'${v:04x}','abx':f'${v:04x},x','aby':f'${v:04x},y','ind':f'(${v:04x})','izx':f'(${v:02x},x)','izy':f'(${v:02x}),y','rel':f'${(a+2+(v-256 if v>127 else v)):04x}'}[m]
    print(f'{a:04x} {n} {s}'); a+=1+l
