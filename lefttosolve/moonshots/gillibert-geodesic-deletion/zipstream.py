import sys, struct, zlib
# Streaming unzip from stdin: writes contents of members whose name ends with a given suffix (and not in __MACOSX) to stdout.
# Handles entries with data descriptors (sizes unknown) by inflating until end-of-stream.
suffix=sys.argv[1].encode()
inp=sys.stdin.buffer; out=sys.stdout.buffer; log=sys.stderr
buf=b''; total=0
def need(k):
    global buf, total
    while len(buf)<k:
        chunk=inp.read(1<<20)
        if not chunk: return False
        buf+=chunk; total+=len(chunk)
    return True
nmem=0
while True:
    if not need(30): break
    if buf[:4]!=b'PK\x03\x04':
        # resync: search for next local header; stop at central directory
        if buf[:4]==b'PK\x01\x02' or buf[:4]==b'PK\x05\x06': break
        i=buf.find(b'PK\x03\x04',1)
        j=buf.find(b'PK\x01\x02',1)
        if j>=0 and (i<0 or j<i): break
        if i<0:
            buf=buf[-3:]
            if not need(4+3): break
            continue
        buf=buf[i:]; continue
    sig,ver,flag,comp,mt,md,crc,csize,usize,nlen,elen=struct.unpack('<IHHHHHIIIHH',buf[:30])
    if not need(30+nlen+elen): break
    name=buf[30:30+nlen]
    buf=buf[30+nlen+elen:]
    want = name.endswith(suffix) and not name.startswith(b'__MACOSX')
    if comp==8:
        dec=zlib.decompressobj(-15)
        while not dec.eof:
            if not buf:
                if not need(1): break
            data=dec.decompress(buf)
            buf=dec.unused_data if dec.eof else b''
            if want and data: out.write(data)
        if want: 
            out.write(b'\n'); nmem+=1
            log.write('member %s done, %d bytes read\n'%(name.decode('latin1'),total)); log.flush()
    elif comp==0:
        if not need(csize): break
        if want: out.write(buf[:csize]+b'\n')
        buf=buf[csize:]
    else:
        log.write('unsupported compression %d\n'%comp); break
out.flush()
log.write('zipstream finished: %d members, %d bytes\n'%(nmem,total))
